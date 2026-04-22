import Contracts.Common

namespace Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment

open Verity hiding pure bind
open Verity.EVM.Uint256

/--
  Focused Verity slice of TermMax `TermMaxOrderV2` for invariant 1 on the
  `debtToken -> XT` exact-input path.

  What was simplified | Why
  - `CurveCut[]` is reduced to one active lend-side cut passed as direct params |
    the current `verity_contract` array surface only supports one-word element
    arrays, while `CurveCut[]` is an array of structs; the exact multi-segment
    path would also need executable iteration over struct-array elements.
  - Only the `swapExactTokenToToken(debtToken, xt, ...)` branch is modeled |
    invariant 1 only needs the pricing-state transition for one successful path;
    the other seven swap branches are orthogonal.
  - Token transfers, callback hooks, pool rebalancing, GT issuance, and event
    emission are omitted | they do not affect the `virtualXtReserve` write that
    the theorem proves.
  - `daysToMaturity` and fee ratios are direct parameters |
    the real contract reads them from `_daysToMaturity()` and market config;
    passing them in keeps the pricing math exact while avoiding unrelated
    external-state modeling.
  - `_buyXtStep` / `_buyToken` / `_swapAndUpdateReserves` are inlined into one
    executable entrypoint | current executable `verity_contract` bodies still do
    not accept internal helper-call binds like `let b ← helper a`, so keeping
    the Solidity helper stack literally would require unsupported internal-call
    execution.
  Within that slice, the arithmetic and control flow follow `_buyXtStep`,
  `_buyToken`, and `_swapAndUpdateReserves` line by line.

  Upstream: term-structure/termmax-contract-v2@64bd47b98e064c7fb91ab4a59b70520e0ec285d5
  File: contracts/v2/TermMaxOrderV2.sol
-/

def DECIMAL_BASE : Uint256 := 100000000
def DAYS_IN_YEAR : Uint256 := 365
def SIGNED_INT256_BOUND : Uint256 :=
  57896044618658097711785492504343953926634992332820282019728792003956564819968

def isNegativeInt256Word (word : Uint256) : Bool :=
  word >= SIGNED_INT256_BOUND

def signedReserveOffset (reserve offsetWord : Uint256) : Uint256 :=
  if isNegativeInt256Word offsetWord then
    sub reserve (sub 0 offsetWord)
  else
    add reserve offsetWord

def singleSegmentScaledLiqSquare
    (daysToMaturity borrowTakerFeeRatio cutLiqSquare : Uint256) : Uint256 :=
  let nif := add DECIMAL_BASE borrowTakerFeeRatio
  div (mul (mul cutLiqSquare daysToMaturity) nif) (mul DAYS_IN_YEAR DECIMAL_BASE)

def singleSegmentVirtualFtReserve
    (daysToMaturity oriXtReserve borrowTakerFeeRatio cutLiqSquare cutOffsetWord : Uint256) : Uint256 :=
  let liqSquare := singleSegmentScaledLiqSquare daysToMaturity borrowTakerFeeRatio cutLiqSquare
  let vXtReserve := signedReserveOffset oriXtReserve cutOffsetWord
  div liqSquare vXtReserve

def singleSegmentBuyXtTokenAmtOut
    (daysToMaturity oriXtReserve debtTokenAmtIn borrowTakerFeeRatio cutLiqSquare cutOffsetWord : Uint256) :
    Uint256 :=
  let liqSquare := singleSegmentScaledLiqSquare daysToMaturity borrowTakerFeeRatio cutLiqSquare
  let vXtReserve := signedReserveOffset oriXtReserve cutOffsetWord
  let vFtReserve := div liqSquare vXtReserve
  sub vXtReserve (div liqSquare (add vFtReserve debtTokenAmtIn))

verity_contract TermMaxOrderV2BuyXtSingleSegment where
  storage
    virtualXtReserve : Uint256 := slot 0

  /-
    Models the successful exact-input `debtToken -> XT` pricing path:

    `swapExactTokenToToken` (debtToken, xt)
      -> `_swapAndUpdateReserves(..., _buyXt)`
      -> `_buyToken(..., _buyXtStep)`

    The single active lend cut is provided directly as the three `CurveCut`
    fields:
    - `cutXtReserve` corresponds to `cuts[0].xtReserve`
    - `cutLiqSquare` corresponds to `cuts[0].liqSquare`
    - `cutOffsetWord` is the signed `cuts[0].offset`, encoded as the same
      two's-complement EVM word used by Solidity `int256`
  -/
  function swapDebtTokenToXtExactInSingleSegment
      (daysToMaturity : Uint256, debtTokenAmtIn : Uint256, minTokenOut : Uint256,
       borrowTakerFeeRatio : Uint256, lendMakerFeeRatio : Uint256,
       cutXtReserve : Uint256, cutLiqSquare : Uint256, cutOffsetWord : Uint256) : Uint256 := do
    let oriXtReserve ← getStorage virtualXtReserve
    require (debtTokenAmtIn != 0) "ZeroInput"
    require (cutXtReserve == 0) "SingleSegmentOnly"

    let negativeOffset :=
      cutOffsetWord >= 57896044618658097711785492504343953926634992332820282019728792003956564819968
    let signedOffsetSafe := ite negativeOffset
      (sub 0 cutOffsetWord <= oriXtReserve)
      (add oriXtReserve cutOffsetWord >= oriXtReserve)
    require signedOffsetSafe "SignedOffsetUnsafe"
    let nif := add 100000000 borrowTakerFeeRatio
    let liqSquare := div (mul (mul cutLiqSquare daysToMaturity) nif) (mul 365 100000000)
    let vXtReserve := ite negativeOffset
      (sub oriXtReserve (sub 0 cutOffsetWord))
      (add oriXtReserve cutOffsetWord)
    require (vXtReserve != 0) "ZeroVirtualXtReserve"
    let vFtReserve := div liqSquare vXtReserve
    let tokenAmtOut := sub vXtReserve (div liqSquare (add vFtReserve debtTokenAmtIn))
    require (tokenAmtOut <= oriXtReserve) "CurveCutCrossed"
    let curveDeltaFt := debtTokenAmtIn
    let feeAmt := sub curveDeltaFt (div (mul curveDeltaFt (sub 100000000 lendMakerFeeRatio)) nif)
    let _deltaFt := sub curveDeltaFt feeAmt
    let netOut := add tokenAmtOut debtTokenAmtIn
    require (netOut >= minTokenOut) "InsufficientTokenOut"

    setStorage virtualXtReserve (sub oriXtReserve tokenAmtOut)
    return netOut

end Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment
