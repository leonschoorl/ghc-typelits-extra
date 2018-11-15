# Changelog for the [`ghc-typelits-extra`](http://hackage.haskell.org/package/ghc-typelits-extra) package

# ??
* Reduce `a <=? Max a b` to `True`

# 0.3 *September 14th 2018*
* Move `KnownNat2` instances for GHC 8.4's `Div` and `Mod` from `ghc-typelits-extra` to `ghc-typelits-knownnat`

# 0.2.6 *Julty 10th 2018*
* Add support for GHC-8.6.1-alpha1

# 0.2.5 *May 9th 2018*
* Add support for ghc-typelits-natnormalise-0.6

# 0.2.4 *January 4th 2018*
* Add support for GHC-8.4.1-alpha1

# 0.2.3 *May 15th 2017*
* Support GHC 8.2
* `Max`, `Min`, `GCD`, and `LCM` now have a commutativity property [#9](https://github.com/clash-lang/ghc-typelits-extra/issues/9)
* Reduce `GCD 0 x` to `x` [#9](https://github.com/clash-lang/ghc-typelits-extra/issues/9)
* Reduce `GCD 1 x` to `1` [#9](https://github.com/clash-lang/ghc-typelits-extra/issues/9)
* Reduce `GCD x x` to `x` [#9](https://github.com/clash-lang/ghc-typelits-extra/issues/9)
* Reduce `LCM 0 x` to `0` [#9](https://github.com/clash-lang/ghc-typelits-extra/issues/9)
* Reduce `LCM 1 x` to `x` [#9](https://github.com/clash-lang/ghc-typelits-extra/issues/9)
* Reduce `LCM x x` to `x` [#9](https://github.com/clash-lang/ghc-typelits-extra/issues/9)
* Reduce `Max (0-1) 0` to `0` [#10](https://github.com/clash-lang/ghc-typelits-extra/issues/10)
* Reduce `Min (0-1) 0` to `0 - 1` [#10](https://github.com/clash-lang/ghc-typelits-extra/issues/10)
* Fixes bugs:
  * Solver turns LCM into GCD [#8](https://github.com/clash-lang/ghc-typelits-extra/issues/8)
  * Solver turns Max into Min

# 0.2.2 *January 15th 2017*
* Reduce `Min n (n+1)` to `n`
* Reduce `Max n (n+1)` to `n+1`
* Reduce cases like `1 <=? Div 18 6` to `True`
* Add a type-level division that rounds up: `type DivRU n d = Div (n + (d - 1)) d`
* Add a type-level `divMod` : `DivMod :: Nat -> Nat -> '(Nat, Nat)`

# 0.2.1 *September 29th 2016*
* Reduce `Max n n` to `n`
* Reduce `Min n n` to `n`

# 0.2 *August 19th 2016*
* New type-level operations:
  * `Max`: type-level `max`
  * `Min`: type-level `min`
  * `Div`: type-level `div`
  * `Mod`: type-level `mod`
  * `FLog`: floor of logBase
  * `Log`: exact integer logBase (i.e. where `floor (logBase b x) ~ ceiling (logBase b x)` holds)
  * `LCM`: type-level `lcm`
* Fixes bugs:
  * `CLog b 1` doesn't reduce to `0`

## 0.1.3 *July 19th 2016*
* Fixes bugs:
  * Rounding error in `CLog` calculation

## 0.1.2 *July 8th 2016*
* Solve KnownNat constraints over CLog and GCD, i.e., KnownNat (CLog 2 4)

## 0.1.1 *January 20th 2016*
* Compile on GHC 8.0+

## 0.1 *October 21st 2015*
* Initial release
