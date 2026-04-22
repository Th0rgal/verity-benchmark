import Contracts.Common

namespace Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment

open Verity hiding pure bind
open Verity.EVM.Uint256

/--
  Focused Verity slice of TermMax `TermMaxOrderV2` for invariant 1 on the
  `debtToken -> XT` exact-input path.

  What was simplified | Why
  - `CurveCut[]` is reduced to one active lend-side cut passed as direct params |
    current Verity storage dynamic arrays still support only one-word element
    types on the macro path, so `CurveCut[]` cannot be represented faithfully as
    an array of structs yet.
  - `_buyToken` and `_swapAndUpdateReserves` are specialized to the concrete
    `_buyXtStep` / `_buyXt` path instead of taking Solidity function-pointer
    parameters | direct internal helper calls are now supported in Verity, but
    Solidity-style higher-order function parameters are still not part of the
    executable `verity_contract` surface.
  - Only the `swapExactTokenToToken(debtToken, xt, ...)` branch is modeled |
    the requested invariant only concerns the successful exact-input borrow path;
    the other swap branches are orthogonal.
  - Token transfers, callback hooks, pool rebalancing, GT issuance, and event
    emission are omitted | they do not affect the `virtualXtReserve` write that
    the theorem proves.
  - The specialized helpers drop the explicit `isNegativeXt` return flag |
    on the chosen `_buyXt` path that flag is a constant `true`, so carrying it
    through every helper return only adds unreachable-branch noise without
    changing the state transition semantics of this slice.

  Within those declared simplifications, the helper stack now mirrors the
  Solidity source shape closely:

  `swapExactTokenToToken(debtToken, xt)` ->
  `_swapAndUpdateReserves(..., _buyXt)` ->
  `_buyXt` ->
  `_buyToken(..., _buyXtStep)` ->
  `TermMaxCurve.buyXt` ->
  `cutsReverseIter` ->
  `calcIntervalProps`

  Upstream: term-structure/termmax-contract-v2@64bd47b98e064c7fb91ab4a59b70520e0ec285d5
  Files:
  - contracts/v2/TermMaxOrderV2.sol
  - contracts/v1/lib/TermMaxCurve.sol
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
    (daysToMaturity oriXtReserve borrowTakerFeeRatio cutLiqSquare cutOffsetWord : Uint256) :
    Uint256 :=
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

def singleSegmentBuyXtFeeAmt
    (debtTokenAmtIn borrowTakerFeeRatio lendMakerFeeRatio : Uint256) : Uint256 :=
  let nif := add DECIMAL_BASE borrowTakerFeeRatio
  sub debtTokenAmtIn
    (div (mul debtTokenAmtIn (sub DECIMAL_BASE lendMakerFeeRatio)) nif)

def singleSegmentBuyXtNetOut
    (daysToMaturity oriXtReserve debtTokenAmtIn borrowTakerFeeRatio cutLiqSquare cutOffsetWord : Uint256) :
    Uint256 :=
  add
    (singleSegmentBuyXtTokenAmtOut
      daysToMaturity
      oriXtReserve
      debtTokenAmtIn
      borrowTakerFeeRatio
      cutLiqSquare
      cutOffsetWord)
    debtTokenAmtIn

verity_contract TermMaxOrderV2BuyXtSingleSegment where
  storage
    virtualXtReserve : Uint256 := slot 0

  /-
    Specialized `TermMaxCurve.calcIntervalProps` for the one active lend-side
    cut carried directly as scalar parameters.
  -/
  function calcIntervalProps
      (daysToMaturity : Uint256, oriXtReserve : Uint256,
       borrowTakerFeeRatio : Uint256, cutLiqSquare : Uint256, cutOffsetWord : Uint256) :
      Tuple [Uint256, Uint256, Uint256] := do
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
    return (liqSquare, vXtReserve, vFtReserve)

  /-
    Single-cut specialization of `TermMaxCurve.cutsReverseIter(..., buyXtStep)`.
    Because the slice exposes exactly one active cut and requires its
    `xtReserve` to be zero, crossing the segment boundary becomes the same
    condition as asking for more XT than the current reserve can provide.
  -/
  function cutsReverseIter
      (daysToMaturity : Uint256, oriXtReserve : Uint256, debtTokenAmtIn : Uint256,
       borrowTakerFeeRatio : Uint256, cutXtReserve : Uint256,
       cutLiqSquare : Uint256, cutOffsetWord : Uint256) :
      Tuple [Uint256, Uint256] := do
    require (cutXtReserve == 0) "SingleSegmentOnly"
    let (liqSquare, vXtReserve, vFtReserve) ←
      calcIntervalProps
        daysToMaturity
        oriXtReserve
        borrowTakerFeeRatio
        cutLiqSquare
        cutOffsetWord
    let tokenAmtOut := sub vXtReserve (div liqSquare (add vFtReserve debtTokenAmtIn))
    require (tokenAmtOut <= oriXtReserve) "CurveCutCrossed"
    return (tokenAmtOut, debtTokenAmtIn)

  /-
    Single-cut specialization of `TermMaxCurve.buyXt`.
  -/
  function buyXtCurve
      (daysToMaturity : Uint256, oriXtReserve : Uint256, debtTokenAmtIn : Uint256,
       borrowTakerFeeRatio : Uint256, cutXtReserve : Uint256,
       cutLiqSquare : Uint256, cutOffsetWord : Uint256) :
      Tuple [Uint256, Uint256] := do
    let (negDeltaXt, deltaFt) ←
      cutsReverseIter
        daysToMaturity
        oriXtReserve
        debtTokenAmtIn
        borrowTakerFeeRatio
        cutXtReserve
        cutLiqSquare
        cutOffsetWord
    return (negDeltaXt, deltaFt)

  /-
    Corresponds to Solidity `_buyXtStep`.
  -/
  function buyXtStep
      (daysToMaturity : Uint256, oriXtReserve : Uint256, debtTokenAmtIn : Uint256,
       borrowTakerFeeRatio : Uint256, lendMakerFeeRatio : Uint256,
       cutXtReserve : Uint256, cutLiqSquare : Uint256, cutOffsetWord : Uint256) :
      Tuple [Uint256, Uint256, Uint256, Uint256] := do
    let (tokenAmtOut, curveDeltaFt) ←
      buyXtCurve
        daysToMaturity
        oriXtReserve
        debtTokenAmtIn
        borrowTakerFeeRatio
        cutXtReserve
        cutLiqSquare
        cutOffsetWord
    let nif := add 100000000 borrowTakerFeeRatio
    let feeAmt := sub curveDeltaFt
      (div (mul curveDeltaFt (sub 100000000 lendMakerFeeRatio)) nif)
    let deltaFt := sub curveDeltaFt feeAmt
    let deltaXt := tokenAmtOut
    return (tokenAmtOut, feeAmt, deltaFt, deltaXt)

  /-
    Corresponds to Solidity `_buyToken`, specialized to the `_buyXtStep`
    function-pointer argument.
  -/
  function buyToken
      (daysToMaturity : Uint256, oriXtReserve : Uint256, debtTokenAmtIn : Uint256,
       minTokenOut : Uint256, borrowTakerFeeRatio : Uint256, lendMakerFeeRatio : Uint256,
       cutXtReserve : Uint256, cutLiqSquare : Uint256, cutOffsetWord : Uint256) :
      Tuple [Uint256, Uint256, Uint256, Uint256] := do
    let (tokenAmtOut, feeAmt, deltaFt, deltaXt) ←
      buyXtStep
        daysToMaturity
        oriXtReserve
        debtTokenAmtIn
        borrowTakerFeeRatio
        lendMakerFeeRatio
        cutXtReserve
        cutLiqSquare
        cutOffsetWord
    let netOut := add tokenAmtOut debtTokenAmtIn
    require (netOut >= minTokenOut) "InsufficientTokenOut"
    return (netOut, feeAmt, deltaFt, deltaXt)

  /-
    Corresponds to Solidity `_buyXt`.
  -/
  function buyXt
      (daysToMaturity : Uint256, oriXtReserve : Uint256, debtTokenAmtIn : Uint256,
       minTokenOut : Uint256, borrowTakerFeeRatio : Uint256, lendMakerFeeRatio : Uint256,
       cutXtReserve : Uint256, cutLiqSquare : Uint256, cutOffsetWord : Uint256) :
      Tuple [Uint256, Uint256, Uint256, Uint256] := do
    let (netOut, feeAmt, deltaFt, deltaXt) ←
      buyToken
        daysToMaturity
        oriXtReserve
        debtTokenAmtIn
        minTokenOut
        borrowTakerFeeRatio
        lendMakerFeeRatio
        cutXtReserve
        cutLiqSquare
        cutOffsetWord
    return (netOut, feeAmt, deltaFt, deltaXt)

  /-
    Corresponds to Solidity `_swapAndUpdateReserves`, specialized to the
    `_buyXt` function-pointer argument.
  -/
  function swapAndUpdateReserves
      (daysToMaturity : Uint256, debtTokenAmtIn : Uint256, minTokenOut : Uint256,
       borrowTakerFeeRatio : Uint256, lendMakerFeeRatio : Uint256,
       cutXtReserve : Uint256, cutLiqSquare : Uint256, cutOffsetWord : Uint256) :
      Tuple [Uint256, Uint256, Uint256, Uint256] := do
    let oriXtReserve ← getStorage virtualXtReserve
    let (netAmt, feeAmt, deltaFt, deltaXt) ←
      buyXt
        daysToMaturity
        oriXtReserve
        debtTokenAmtIn
        minTokenOut
        borrowTakerFeeRatio
        lendMakerFeeRatio
        cutXtReserve
        cutLiqSquare
        cutOffsetWord
    let newXtReserve ← getStorage virtualXtReserve
    setStorage virtualXtReserve (sub newXtReserve deltaXt)
    return (netAmt, feeAmt, deltaFt, deltaXt)

  /-
    Models the successful exact-input `debtToken -> XT` pricing path:

    `swapExactTokenToToken` (debtToken, xt)
      -> `_swapAndUpdateReserves(..., _buyXt)`
      -> `_buyXt`
      -> `_buyToken(..., _buyXtStep)`
  -/
  function swapDebtTokenToXtExactInSingleSegment
      (daysToMaturity : Uint256, debtTokenAmtIn : Uint256, minTokenOut : Uint256,
       borrowTakerFeeRatio : Uint256, lendMakerFeeRatio : Uint256,
       cutXtReserve : Uint256, cutLiqSquare : Uint256, cutOffsetWord : Uint256) : Uint256 := do
    require (debtTokenAmtIn != 0) "ZeroInput"
    let (netTokenOut, _feeAmt, _deltaFt, _deltaXt) ←
      swapAndUpdateReserves
        daysToMaturity
        debtTokenAmtIn
        minTokenOut
        borrowTakerFeeRatio
        lendMakerFeeRatio
        cutXtReserve
        cutLiqSquare
        cutOffsetWord
    return netTokenOut

end Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment
