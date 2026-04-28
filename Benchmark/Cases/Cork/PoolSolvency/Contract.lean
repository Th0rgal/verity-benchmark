import Contracts.Common

namespace Benchmark.Cases.Cork.PoolSolvency

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Focused Verity slice of Cork Phoenix `unwindExerciseOther`.

  The solvency invariant (Certora P-02) states that locked collateral,
  normalized to 18 decimals, must cover the outstanding swap share supply:

    collateralAssetLocked * colScaleUp >= swapTotalSupply - swapBalanceOfPool

  Certora verified this for all CorkPool functions EXCEPT
  `unwindExerciseOther`, which timed out. Certora also restricted the
  exchange rate to 1 or 3*1e18 and decimals to 17/16. This model proves
  solvency for arbitrary exchange rates and decimal combinations.

  Upstream: Cork-Technology/phoenix (v1.1.2)
  Files: contracts/libraries/PoolLib.sol (previewUnwindExerciseOther)
         contracts/libraries/MathHelper.sol (calculateEqualSwapAmount)
         contracts/libraries/TransferHelper.sol (tokenNativeDecimalsToFixed,
           normalizeDecimalsWithCeilDiv)
         contracts/core/CorkPoolManager.sol (_unwindExercise)

  Simplifications
  ----------------
  What was simplified: struct State fields flattened to individual storage slots.
  Why: Verity lacks nested struct storage. (Verity gap)

  What was simplified: external token transfers (safeTransfer, safeTransferFrom)
  and oracle rate update (_getLatestApplicableRateAndUpdate) elided.
  Why: trusted boundaries; model captures only state-changing arithmetic.

  What was simplified: time-decay fee factored out. Net effect on
  collateralAssetLocked modeled directly as += assetsInWithoutFee.
  This is exact: the Solidity does locked += collateralAssetsIn then
  locked -= fee via _unlockTo, and collateralAssetsIn - fee =
  assetsInWithoutFee by construction in calculateGrossAmountWithTimeDecayFee.
  Why: avoids modeling the full time-decay fee pipeline (computeT, feeFactor,
  gross amount markup) while preserving the exact net state change.

  What was simplified: access control, reentrancy guard, event emissions elided.
  Why: orthogonal to solvency arithmetic.

  What was simplified: 10^(18-decimals) modeled via pre-computed scale factor
  parameters (refScaleUp, colScaleUp) instead of runtime exponentiation.
  Why: Verity has no Uint256 pow function. (Verity gap)
  The scale factors are constants per market (decimals are set at pool creation).

  What was simplified: normalizeDecimalsWithCeilDiv(R, refDec, colDec) expressed
  as ceilDiv(tokenNativeDecimalsToFixed(R, refDec), colScaleUp).
  This is mathematically equivalent because ceil(R*a / (a*b)) = ceil(R / b)
  for positive a.
  Why: unifies the three decimal-relationship cases (refDec > colDec, <, =)
  into one formula using the existing scale factor parameters.
-/

/-- MathHelper.calculateEqualSwapAmount: amount = referenceAsset * swapRate / 1e18 (floor).
    Solidity: referenceAsset.mulDiv(swapRate, 1e18, Math.Rounding.Floor) -/
def calculateEqualSwapAmount (referenceAsset swapRate : Uint256) : Uint256 :=
  mulDivDown referenceAsset swapRate 1000000000000000000

/-- TransferHelper.tokenNativeDecimalsToFixed: scales from native decimals to 18 decimals.
    Solidity: normalizeDecimals(amount, decimals, 18) = amount * 10^(18-decimals).
    Here refScaleUp = 10^(18-decimals) is pre-computed. -/
def tokenNativeDecimalsToFixed (amount refScaleUp : Uint256) : Uint256 :=
  mul amount refScaleUp

/-- TransferHelper.normalizeDecimalsWithCeilDiv: converts between decimal scales with
    ceiling rounding. Expressed as ceilDiv(amount_in_18dec, colScaleUp) which is
    equivalent to the three-branch Solidity version for all decimal relationships. -/
def normalizeDecimalsWithCeilDiv (amountFixed colScaleUp : Uint256) : Uint256 :=
  ceilDiv amountFixed colScaleUp

/-- Math.mulDiv with Ceil rounding: ceil(a * b / c).
    Solidity: a.mulDiv(b, c, Math.Rounding.Ceil) -/
def mulDivCeil (a b c : Uint256) : Uint256 :=
  mulDivUp a b c

verity_contract CorkUnwindExerciseOther where
  storage
    -- state.pool.balances.collateralAsset.locked (collateral-native decimals)
    collateralAssetLocked : Uint256 := slot 0
    -- IERC20(state.shares.swap).totalSupply() (18 decimals, constant during unwind)
    swapTotalSupply : Uint256 := slot 1
    -- IERC20(state.shares.swap).balanceOf(address(this)) (18 decimals)
    swapBalanceOfPool : Uint256 := slot 2
    -- IConstraintRateAdapter(adapter).previewAdjustedRate(poolId) (18 decimals)
    swapRate : Uint256 := slot 3
    -- 10^(18 - referenceDecimals), pre-computed scale factor
    refScaleUp : Uint256 := slot 4
    -- 10^(18 - collateralDecimals), pre-computed scale factor
    colScaleUp : Uint256 := slot 5

  /-
    Models the solvency-critical arithmetic of unwindExerciseOther.

    Solidity (PoolLib.previewUnwindExerciseOther + CorkPoolManager._unwindExercise):

      // Step 1: cstSharesOut = calculateEqualSwapAmount(
      //   tokenNativeDecimalsToFixed(referenceAssetsOut, refDec), swapRate)
      uint256 refFixed = referenceAssetsOut * refScaleUp;
      uint256 cstSharesOut = refFixed.mulDiv(swapRate, 1e18, Floor);

      // Step 2: normalizedReferenceAsset = normalizeDecimalsWithCeilDiv(
      //   referenceAssetsOut, refDec, colDec)
      uint256 normalizedReferenceAsset = ceilDiv(refFixed, colScaleUp);

      // Step 3: assetsInWithoutFee = normalizedReferenceAsset.mulDiv(
      //   swapRate, 1e18, Ceil)
      uint256 assetsInWithoutFee = mulDivCeil(normalizedReferenceAsset, swapRate, 1e18);

      // Step 4: state mutation (net of fee — see doc-comment above)
      collateralAssetLocked += assetsInWithoutFee;
      swapBalanceOfPool -= cstSharesOut;
  -/
  function unwindExerciseOther (referenceAssetsOut : Uint256) : Uint256 := do
    let collateralAssetLocked_ ← getStorage collateralAssetLocked
    let swapBalanceOfPool_ ← getStorage swapBalanceOfPool
    let swapRate_ ← getStorage swapRate
    let refScaleUp_ ← getStorage refScaleUp
    let colScaleUp_ ← getStorage colScaleUp

    -- tokenNativeDecimalsToFixed(referenceAssetsOut, refDec)
    let refFixed := mul referenceAssetsOut refScaleUp_

    -- calculateEqualSwapAmount(refFixed, swapRate)
    let cstSharesOut := div (mul refFixed swapRate_) 1000000000000000000

    -- normalizeDecimalsWithCeilDiv(referenceAssetsOut, refDec, colDec)
    let normalizedReferenceAsset := ite (refFixed == 0) 0
      (add (div (sub refFixed 1) colScaleUp_) 1)

    -- Math.mulDiv(normalizedReferenceAsset, swapRate, 1e18, Ceil)
    let assetProduct := mul normalizedReferenceAsset swapRate_
    let assetsInWithoutFee := ite (assetProduct == 0) 0
      (add (div (sub assetProduct 1) 1000000000000000000) 1)

    -- require(cstSharesOut <= swapTokenBalance, InsufficientLiquidity(...))
    require (cstSharesOut <= swapBalanceOfPool_) "InsufficientLiquidity"

    -- state mutation (net of fee)
    setStorage collateralAssetLocked (add collateralAssetLocked_ assetsInWithoutFee)
    setStorage swapBalanceOfPool (sub swapBalanceOfPool_ cstSharesOut)

    return cstSharesOut

end Benchmark.Cases.Cork.PoolSolvency
