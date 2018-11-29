{-# LANGUAGE CPP, DataKinds, TypeOperators, TypeApplications, TypeFamilies #-}
#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE NoStarIsType #-}
#endif
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver #-}

import Data.Proxy
import Data.Type.Bool

import GHC.TypeLits
import GHC.TypeLits.Extra


-- ok
-- test1 :: (c ~ b, a ~ c, b ~ (Max x y)) => Proxy x -> Proxy y -> Proxy (a <=? b) -> Proxy True
-- test1 _ _ = id


-- ok
-- test1 :: Proxy x -> Proxy y -> Proxy ((Max x y) <=? (Max x (Max x y))) -> Proxy True
-- test1 _ _ = id

-- ok, not solved -typelits-extra, but by -typelits-natnormalise
-- test1 :: Proxy x -> Proxy y -> Proxy (Max x y <=? (Max x y + 1)) -> Proxy True
-- test1 _ _ = id

-- not
test1 :: Proxy x -> Proxy y -> Proxy (Max y x <=? (Max x y + 1)) -> Proxy True
test1 _ _ = id

-- not
-- test1 :: Proxy x -> Proxy y -> Proxy ((Max x y) <=? (Max x (Max x y) + 1)) -> Proxy True
-- test1 _ _ = id


main :: IO ()
main = return ()
