{-# LANGUAGE TypeOperators,DataKinds #-}
{-# OPTIONS_GHC -fplugin=GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin=GHC.TypeLits.Normalise #-}

module Test where
import GHC.TypeLits.Extra
import GHC.TypeLits
import Data.Proxy
import Prelude

g0 :: Proxy n
   -> Proxy (2 <=? Max (3+n) 1)
   -> Proxy True
g0 _ = id


-- h0 :: Proxy n
--    -> Proxy (2 <=? (2+n))
--    -> Proxy True
-- h0 _ = id
