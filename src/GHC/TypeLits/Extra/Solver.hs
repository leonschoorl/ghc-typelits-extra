{-|
Copyright  :  (C) 2015-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

To use the plugin, add the

@
{\-\# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver \#-\}
@

pragma to the header of your file

-}

{-# LANGUAGE CPP           #-}
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.Extra.Solver
  ( plugin )
where

-- external
import Control.Monad             ((<=<))
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Either               (lefts)
import Data.Maybe                (catMaybes)
import GHC.TcPluginM.Extra       (evByFiat, lookupModule, lookupName,
                                  tracePlugin)

-- GHC API
import FastString (fsLit)
import Module     (mkModuleName)
import OccName    (mkTcOcc)
import Outputable (Outputable (..), (<+>), ($$), text)
import Plugins    (Plugin (..), defaultPlugin)
#if MIN_VERSION_ghc(8,6,0)
import Plugins    (purePlugin)
#endif
import TcEvidence (EvTerm)
import TcPluginM  (TcPluginM, tcLookupTyCon, tcPluginTrace, zonkCt)
import TcRnTypes  (Ct, TcPlugin(..), TcPluginResult (..), ctEvidence, ctEvPred,
                   isWantedCt)
import TcType      (typeKind)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred), classifyPredType,
                   eqType)
import TyCoRep    (Type (..))
import TysWiredIn (typeNatKind, promotedTrueDataCon, promotedFalseDataCon)
import TcTypeNats (typeNatLeqTyCon)
#if MIN_VERSION_ghc(8,4,0)
import TcTypeNats (typeNatTyCons)
#endif

-- internal
import GHC.TypeLits.Extra.Solver.Operations
import GHC.TypeLits.Extra.Solver.Unify

import Debug.Trace
import Outputable

-- | A solver implement as a type-checker plugin for:
--
--     * 'Div': type-level 'div'
--
--     * 'Mod': type-level 'mod'
--
--     * 'FLog': type-level equivalent of <https://hackage.haskell.org/package/integer-gmp/docs/GHC-Integer-Logarithms.html#v:integerLogBase-35- integerLogBase#>
--       .i.e. the exact integer equivalent to "@'floor' ('logBase' x y)@"
--
--     * 'CLog': type-level equivalent of /the ceiling of/ <https://hackage.haskell.org/package/integer-gmp/docs/GHC-Integer-Logarithms.html#v:integerLogBase-35- integerLogBase#>
--       .i.e. the exact integer equivalent to "@'ceiling' ('logBase' x y)@"
--
--     * 'Log': type-level equivalent of <https://hackage.haskell.org/package/integer-gmp/docs/GHC-Integer-Logarithms.html#v:integerLogBase-35- integerLogBase#>
--        where the operation only reduces when "@'floor' ('logBase' b x) ~ 'ceiling' ('logBase' b x)@"
--
--     * 'GCD': a type-level 'gcd'
--
--     * 'LCM': a type-level 'lcm'
--
-- To use the plugin, add
--
-- @
-- {\-\# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver \#-\}
-- @
--
-- To the header of your file.
plugin :: Plugin
plugin
  = defaultPlugin
  { tcPlugin = const $ Just normalisePlugin
#if MIN_VERSION_ghc(8,6,0)
  , pluginRecompile = purePlugin
#endif
  }

normalisePlugin :: TcPlugin
normalisePlugin = tracePlugin "ghc-typelits-extra"
  TcPlugin { tcPluginInit  = lookupExtraDefs
           , tcPluginSolve = decideEqualSOP
           , tcPluginStop  = const (return ())
           }

decideEqualSOP :: ExtraDefs -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
decideEqualSOP _    _givens _deriveds []      = return (TcPluginOk [] [])
decideEqualSOP defs givens  _deriveds wanteds = do
  -- GHC 7.10.1 puts deriveds with the wanteds, so filter them out
  let wanteds' = filter isWantedCt wanteds
  unit_wanteds <- catMaybes <$> mapM (runMaybeT . toNatEquality defs) wanteds'
  case unit_wanteds of
    [] -> return (TcPluginOk [] [])
    _  -> do
      unit_givens <- catMaybes <$> mapM ((runMaybeT . toNatEquality defs) <=< zonkCt) givens
      sr <- simplifyExtra (unit_givens ++ unit_wanteds)
      tcPluginTrace "normalised" (ppr sr)
      case sr of
        Simplified evs -> return (TcPluginOk (filter (isWantedCt . snd) evs) [])
        Impossible eq  -> return (TcPluginContradiction [fromNatEquality eq])

type NatEquality   = (Ct,ExtraOp,ExtraOp)
type NatInEquality = (Ct,ExtraOp,ExtraOp,Bool)

data SimplifyResult
  = Simplified [(EvTerm,Ct)]
  | Impossible (Either NatEquality NatInEquality)

instance Outputable SimplifyResult where
  ppr (Simplified evs) = text "Simplified" $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

shout :: String -> a -> a
shout msg = trace (unlines [line,msg,line])
  where line = replicate 40 '='
ppr' :: Outputable a => a -> String
ppr' = showSDocUnsafe . ppr

simplifyExtra :: [Either NatEquality NatInEquality] -> TcPluginM SimplifyResult
simplifyExtra eqs = tcPluginTrace "simplifyExtra" (ppr eqs) >> simples [] eqs
  where
    simples :: [Maybe (EvTerm, Ct)] -> [Either NatEquality NatInEquality] -> TcPluginM SimplifyResult
    simples evs [] = return (Simplified (catMaybes evs))
    simples evs (eq@(Left (ct,u,v)):eqs') = do
      ur <- unifyExtra ct u v
      tcPluginTrace "unifyExtra result" (ppr ur)
      case ur of
        Win  -> simples (((,) <$> evMagic ct <*> pure ct):evs) eqs'
        Lose -> if null evs && null eqs'
                   then return  (Impossible eq)
                   else simples evs eqs'
        Draw -> simples evs eqs'
    simples evs (eq@(Right (ct,u,v,b)):eqs') = do
      tcPluginTrace "unifyExtra leq result" (ppr (u,v,b))
      case (u,v) of
        (I i,I j)
          | (i <= j) == b -> simples (((,) <$> evMagic ct <*> pure ct):evs) eqs'
          | otherwise     -> return  (Impossible eq)
        (p, Max x y)
          | b && (p == x || p == y) -> simples (((,) <$> evMagic ct <*> pure ct):evs) eqs'
          | b && solveMax p x y -> simples (((,) <$> evMagic ct <*> pure ct):evs) eqs'

        -- transform:  q ~ Max x y => (p <=? q ~ True)
        -- to:         (p <=? Max x y) ~ True
        -- and try to solve that along with the rest of the eqs'

        -- problem since GHC-8.4, ghc generates an extra level of indirection
        -- (r ~ Max x y, r ~ q) => (p <=? q ~ True)
        (p, q@(V _))
          --  | b -> case findMax q eqs of
          --          Just m  -> shout (unlines ["findMax: ","q: " ++ show q,"eqs:", unlines $ show <$> eqs, "found m=" ++ show m]) simples evs ((Right (ct,p,m,b)):eqs')
          --          Nothing -> shout (unlines ["findMax: ",show q,show eqs, "not found"]) simples evs eqs'
          | b
          , Just m <- findMax q eqs
          -> simples evs ((Right (ct,p,m,b)):eqs')
        (p, q@(C _)) -> shout ("Don't known C what to do with: " ++ ppr' p ++ " <=? " ++ ppr' q) simples evs eqs'
        _ -> shout ("Don't known what to do with: " ++ ppr' u ++ " <=? " ++ ppr' v) simples evs eqs'

    -- | solveMax p x y returns True when p <= Max x y
    solveMax :: ExtraOp -> ExtraOp -> ExtraOp -> Bool
    solveMax (Max p1 p2) x y | shout "try solveMax met Max on LHS" solveMax p1 x y && solveMax p2 x y = True
    solveMax p (Max x1 x2) _ | solveMax p x1 x2 = True
    solveMax p _ (Max y1 y2) | solveMax p y1 y2 = True
    solveMax p x y           | p == x || p == y = True
    solveMax _ _ _ = False
    -- look for given constraint with the form: c ~ Max x y
    findMax :: ExtraOp -> [Either NatEquality NatInEquality] -> Maybe ExtraOp
    findMax c = go . lefts
      where
        go [] = Nothing
        go ((ct, a,b@(Max _ _)) :_)
          | c == a && not (isWantedCt ct)
            = Just b
        go ((ct, a@(Max _ _),b) :_)
          | c == b && not (isWantedCt ct)
            = Just a
        go ((ct, a,b) :_)
          | c == a && not (isWantedCt ct)
            = Just b
        go ((ct, a,b) :_)
          | c == b && not (isWantedCt ct)
            = Just a
        go (_:rest) = go rest


-- Extract the Nat equality constraints
toNatEquality :: ExtraDefs -> Ct -> MaybeT TcPluginM (Either NatEquality NatInEquality)
toNatEquality defs ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2
      | isNatKind (typeKind t1) || isNatKind (typeKind t2)
      -> Left <$> ((ct,,) <$> normaliseNat defs t1 <*> normaliseNat defs t2)
      | TyConApp tc [x,y] <- t1
      , tc == typeNatLeqTyCon
      , TyConApp tc' [] <- t2
      -> if tc' == promotedTrueDataCon
            then Right <$> ((ct,,,True) <$> normaliseNat defs x <*> normaliseNat defs y)
            else if tc' == promotedFalseDataCon
                 then Right <$> ((ct,,,False) <$> normaliseNat defs x <*> normaliseNat defs y)
                 else fail "Nothing"
    _ -> fail "Nothing"
  where
    isNatKind :: Kind -> Bool
    isNatKind = (`eqType` typeNatKind)

fromNatEquality :: Either NatEquality NatInEquality -> Ct
fromNatEquality (Left (ct, _, _))  = ct
fromNatEquality (Right (ct,_,_,_)) = ct

lookupExtraDefs :: TcPluginM ExtraDefs
lookupExtraDefs = do
    md <- lookupModule myModule myPackage
    ExtraDefs <$> look md "Max"
              <*> look md "Min"
#if MIN_VERSION_ghc(8,4,0)
              <*> pure (typeNatTyCons !! 5)
              <*> pure (typeNatTyCons !! 6)
#else
              <*> look md "Div"
              <*> look md "Mod"
#endif
              <*> look md "FLog"
              <*> look md "CLog"
              <*> look md "Log"
              <*> look md "GCD"
              <*> look md "LCM"
  where
    look md s = tcLookupTyCon =<< lookupName md (mkTcOcc s)
    myModule  = mkModuleName "GHC.TypeLits.Extra"
    myPackage = fsLit "ghc-typelits-extra"

-- Utils
evMagic :: Ct -> Maybe EvTerm
evMagic ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2 -> Just (evByFiat "ghc-typelits-extra" t1 t2)
    _                  -> Nothing
