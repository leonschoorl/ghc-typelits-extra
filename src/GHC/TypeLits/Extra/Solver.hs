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
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Either               (lefts)
import Data.Maybe                (catMaybes)
import Data.Set                  (empty)
import GHC.TcPluginM.Extra       (evByFiat, lookupModule, lookupName,
                                  tracePlugin)
import qualified GHC.TypeLits.Normalise as Normalise

-- GHC API
import FastString (fsLit)
import Module     (mkModuleName)
import OccName    (mkTcOcc)
import Outputable (Outputable (..), (<+>), ($$), showSDocUnsafe, text)
import Plugins    (Plugin (..), defaultPlugin)
#if MIN_VERSION_ghc(8,6,0)
import Plugins    (purePlugin)
#endif
import TcEvidence (EvTerm)
import TcPluginM  (TcPluginM, tcLookupTyCon, tcPluginTrace)
import TcRnTypes  (Ct, TcPlugin(..), TcPluginResult (..), ctEvidence, ctEvPred,
                   isWantedCt)
import TcType      (typeKind)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred), PredType, classifyPredType,
                   eqType, mkPrimEqPred, mkTyConApp)
import TyCoRep    (Type (..))
import TysWiredIn (boolTy, typeNatKind, promotedTrueDataCon, promotedFalseDataCon)
import TcTypeNats (typeNatLeqTyCon)
#if MIN_VERSION_ghc(8,4,0)
import GHC.TcPluginM.Extra (flattenGivens)
import TcTypeNats (typeNatTyCons)
#else
import TcPluginM  (zonkCt)
import Control.Monad ((<=<))
#endif

-- internal
import GHC.TypeLits.Extra.Solver.Operations
import GHC.TypeLits.Extra.Solver.Unify


import GHC.Stack

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
#if MIN_VERSION_ghc(8,4,0)
      unit_givens <- catMaybes <$> mapM (runMaybeT . toNatEquality defs) (givens ++ flattenGivens givens)
#else
      unit_givens <- catMaybes <$> mapM ((runMaybeT . toNatEquality defs) <=< zonkCt) givens
#endif
      sr <- simplifyExtra defs (unit_givens ++ unit_wanteds)
      tcPluginTrace "normalised" (ppr sr)
      case sr of
        Simplified evs newWanted -> return (TcPluginOk (filter (isWantedCt . snd) evs) newWanted)
        Impossible eq  -> return (TcPluginContradiction [fromNatEquality eq])

type NatEquality   = (Ct,ExtraOp,ExtraOp)
type NatInEquality = (Ct,ExtraOp,ExtraOp,Bool)

data SimplifyResult
  = Simplified [(EvTerm,Ct)] [Ct]
  | Impossible (Either NatEquality NatInEquality)

instance Outputable SimplifyResult where
  ppr (Simplified evs newWanted) = text "Simplified" $$ ppr evs $$ ppr newWanted
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

simplifyExtra :: ExtraDefs -> [Either NatEquality NatInEquality] -> TcPluginM SimplifyResult
simplifyExtra defs eqs = tcPluginTrace "simplifyExtra" (ppr eqs) >> simples [] [] eqs
  where
    simples :: [Maybe (EvTerm, Ct)] -> [Ct] -> [Either NatEquality NatInEquality] -> TcPluginM SimplifyResult
    simples evs newWanted [] = return (Simplified (catMaybes evs) newWanted)
    simples evs newWanted (eq@(Left (ct,u,v)):eqs') = do
      ur <- unifyExtra ct u v
      tcPluginTrace "unifyExtra result" (ppr ur)
      case ur of
        Win  -> simples (((,) <$> evMagic ct <*> pure ct):evs) newWanted eqs'
        Lose -> if null evs && null eqs'
                   then return  (Impossible eq)
                   else simples evs newWanted eqs'
        Draw -> simples evs newWanted eqs'
    simples evs newWanted (eq@(Right (ct,u,v,b)):eqs') = do
      tcPluginTrace "unifyExtra leq result" (ppr (u,v,b))
      case (u,v) of
        (I i,I j)
          | (i <= j) == b -> simples (((,) <$> evMagic ct <*> pure ct):evs) newWanted eqs'
          | otherwise     -> return  (Impossible eq)
        (p, Max x y)
          | b && (p == x || p == y) -> simples (((,) <$> evMagic ct <*> pure ct):evs) newWanted eqs'

        -- transform:  q ~ Max x y => (p <=? q ~ True)
        -- to:         (p <=? Max x y) ~ True
        -- and try to solve that along with the rest of the eqs'
        (p, q@(V _))
          | b -> case findMax q eqs of
                   Just m  -> do
                     -- tcPluginTrace "new wanted?" (ppr (ct))
                     -- tcPluginTrace "new wanted2" (ppr (p,m,b))
                     -- _ <- error "new wanted"
                     simples evs newWanted ((Right (ct,p,m,b)):eqs')
                   Nothing -> simples evs newWanted eqs'
        (p,q@(C _)) -> do
          tcPluginTrace "Got C:" (ppr (p,q))
          simples evs newWanted eqs'

        (p, Max x y)
          | Just biggest <- elimMax defs x y -> case biggest of
              C _ -> do
                let pred = ineqToPred defs p biggest b
                Just ((evterm,ctout), newWanted') <- Normalise.evMagic ct empty [pred]
                simples (Just (evterm,ctout):evs) (newWanted' ++ newWanted) eqs'
              _ -> error ("elim max to: " ++ showSDocUnsafe (ppr biggest ))

        (Max x y, p)
          | Just biggest <- elimMax defs x y -> case biggest of
              C _ -> do
                let pred = ineqToPred defs biggest p b
                Just ((evterm,ctout), newWanted') <- Normalise.evMagic ct empty [pred]
                simples (Just (evterm,ctout):evs) (newWanted' ++ newWanted) eqs'
              _ -> error ("elim max to: " ++ showSDocUnsafe (ppr biggest))


        _ -> simples evs newWanted eqs'

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
        go (_:rest) = go rest

ineqToPred :: ExtraDefs -> ExtraOp -> ExtraOp -> Bool -> (PredType,Kind)
ineqToPred defs e1 e2 b = (mkPrimEqPred ineq res,boolTy)
  where
    ty1 = reifyEOP defs e1
    ty2 = reifyEOP defs e2
    ineq = mkTyConApp typeNatLeqTyCon [ty1,ty2]
    res = mkTyConApp tc []
      where tc = case b of
              True  -> promotedTrueDataCon
              False -> promotedFalseDataCon

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
