import Contracts.Common

namespace Benchmark.Cases.Wildcat.BorrowLiquiditySafety

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Focused Verity slice of Wildcat V2 `borrow(uint256 amount)`.

  This benchmark keeps the successful borrow path, the liquidity requirement
  arithmetic from `MarketState.liquidityRequired`, and the final transfer/write
  sequence. The source of truth is Wildcat V2 tag `v2.0.0`
  (`a70f297fbd1b1ab597e0e9a3458a2d13a34b4657`).

  Simplifications
  ----------------
  What was simplified:
  - `asset.balanceOf(address(this))` is modeled as a trusted storage mirror
    `totalAssetsStored`.
  Why:
  - Verity can model low-level external calls, but this benchmark targets the
    borrow/liquidity invariant rather than ERC20 integration mechanics.

  What was simplified:
  - `_getUpdatedState()` is compressed to a single `pendingProtocolFeeDelta`
    applied before the borrow check; the withdrawal-related fields are treated
    as already current at borrow time.
  Why:
  - This is a deliberate benchmark-scope choice. The approved invariant is
    about the successful borrow step preserving liquidity after the market has
    already been updated. Re-modeling the full expiry/payment pipeline would
    broaden the case far beyond the borrow slice.

  What was simplified:
  - The `MathUtils.bipMul` / `MathUtils.rayMul` overflow guards are carried as
    proof preconditions instead of contract-side `require` checks.
  Why:
  - In the pinned local Verity package, `requireSomeUint` only accepts
    `safeAdd` and `safeSub`, not `safeMul`, so the multiplication overflow
    guard cannot be encoded line-by-line inside this `verity_contract` today.

  What was simplified:
  - Wildcat's packed `_state` storage writes are represented as ordinary slots.
  Why:
  - The theorem concerns arithmetic and post-borrow liquidity, not packed-slot
    encoding parity. The semantic field correspondence is preserved explicitly.

  What was simplified:
  - `_isFlaggedByChainalysis`, `hooks.onBorrow`, and `asset.safeTransfer` are
    modeled as trusted boundaries via `borrowerFlagged`, `hookAllowsBorrow`,
    and the `totalAssetsStored` balance update.
  Why:
  - The user marked hooks/access-control as out of scope, but asked that the
    call sites remain structurally visible where practical.
-/

/-- Wildcat math constant: basis points denominator. -/
def BIP : Uint256 := 10000

/-- Half-bip used for round-half-up multiplication. -/
def HALF_BIP : Uint256 := 5000

/-- Wildcat fixed-point scale for normalized/scaled token amounts. -/
def RAY : Uint256 := 1000000000000000000000000000

/-- Half-ray used for round-half-up multiplication. -/
def HALF_RAY : Uint256 := 500000000000000000000000000

/-- Wildcat `satSub`: strictly positive difference or zero. -/
def satSub (a b : Uint256) : Uint256 :=
  if a > b then a - b else 0

/-- Wildcat `bipMul`, using the same round-half-up shape as `MathUtils.bipMul`. -/
def bipMulHalfUp (a b : Uint256) : Uint256 :=
  ((a * b) + HALF_BIP) / BIP

/-- Wildcat `rayMul`, using the same round-half-up shape as `MathUtils.rayMul`. -/
def rayMulHalfUp (a b : Uint256) : Uint256 :=
  ((a * b) + HALF_RAY) / RAY

/-- `MarketState.normalizeAmount(amount)`. -/
def normalizeAmount (scaledAmount scaleFactor : Uint256) : Uint256 :=
  rayMulHalfUp scaledAmount scaleFactor

/-- Outstanding supply is total supply minus pending withdrawals. -/
def outstandingSupply (scaledTotalSupply scaledPendingWithdrawals : Uint256) : Uint256 :=
  scaledTotalSupply - scaledPendingWithdrawals

/-- `MarketState.liquidityRequired()` on the borrow slice's state fields. -/
def liquidityRequiredFromFields
    (scaledTotalSupply scaledPendingWithdrawals normalizedUnclaimedWithdrawals
      accruedProtocolFees reserveRatioBips scaleFactor : Uint256) : Uint256 :=
  let scaledOutstandingSupply := outstandingSupply scaledTotalSupply scaledPendingWithdrawals
  let scaledRequiredReserves :=
    (bipMulHalfUp scaledOutstandingSupply reserveRatioBips) + scaledPendingWithdrawals
  normalizeAmount scaledRequiredReserves scaleFactor +
    accruedProtocolFees +
    normalizedUnclaimedWithdrawals

/-- `MarketState.borrowableAssets(totalAssets)`. -/
def borrowableAssetsFromFields
    (totalAssets scaledTotalSupply scaledPendingWithdrawals normalizedUnclaimedWithdrawals
      accruedProtocolFees reserveRatioBips scaleFactor : Uint256) : Uint256 :=
  satSub totalAssets <|
    liquidityRequiredFromFields
      scaledTotalSupply
      scaledPendingWithdrawals
      normalizedUnclaimedWithdrawals
      accruedProtocolFees
      reserveRatioBips
      scaleFactor

verity_contract BorrowLiquiditySafety where
  storage
    -- Trusted mirror of `asset.balanceOf(address(this))`.
    totalAssetsStored : Uint256 := slot 0
    -- MarketState.isClosed
    isClosed : Uint256 := slot 1
    -- MarketState.accruedProtocolFees
    accruedProtocolFees : Uint256 := slot 2
    -- MarketState.normalizedUnclaimedWithdrawals
    normalizedUnclaimedWithdrawals : Uint256 := slot 3
    -- MarketState.scaledTotalSupply
    scaledTotalSupply : Uint256 := slot 4
    -- MarketState.scaledPendingWithdrawals
    scaledPendingWithdrawals : Uint256 := slot 5
    -- MarketState.reserveRatioBips
    reserveRatioBips : Uint256 := slot 6
    -- MarketState.scaleFactor
    scaleFactor : Uint256 := slot 7
    -- Compressed stand-in for fees applied by `_getUpdatedState()`.
    pendingProtocolFeeDelta : Uint256 := slot 8
    -- Trusted boundary for `_isFlaggedByChainalysis(borrower)`.
    borrowerFlagged : Uint256 := slot 9
    -- Trusted boundary for `hooks.onBorrow(amount, state)`.
    hookAllowsBorrow : Uint256 := slot 10

  /-
    Models the successful path of Wildcat `borrow(uint256 amount)`:
      1. sanctioned-borrower guard
      2. updated state materialization
      3. closed-market guard
      4. borrowable-assets check
      5. hook boundary
      6. transfer boundary
      7. state write
  -/
  function borrow (amount : Uint256) : Unit := do
    let borrowerFlagged_ ← getStorage borrowerFlagged
    require (borrowerFlagged_ == 0) "BorrowWhileSanctioned"

    let totalAssets_ ← getStorage totalAssetsStored
    let isClosed_ ← getStorage isClosed
    let accruedProtocolFees_ ← getStorage accruedProtocolFees
    let normalizedUnclaimedWithdrawals_ ← getStorage normalizedUnclaimedWithdrawals
    let scaledTotalSupply_ ← getStorage scaledTotalSupply
    let scaledPendingWithdrawals_ ← getStorage scaledPendingWithdrawals
    let reserveRatioBips_ ← getStorage reserveRatioBips
    let scaleFactor_ ← getStorage scaleFactor
    let pendingProtocolFeeDelta_ ← getStorage pendingProtocolFeeDelta
    let hookAllowsBorrow_ ← getStorage hookAllowsBorrow

    -- Compressed `_getUpdatedState()`: apply the already-computed fee delta.
    let updatedAccruedProtocolFees_ ← requireSomeUint
      (safeAdd accruedProtocolFees_ pendingProtocolFeeDelta_)
      "ProtocolFeeOverflow"

    require (isClosed_ == 0) "BorrowFromClosedMarket"

    let scaledOutstandingSupply_ ← requireSomeUint
      (safeSub scaledTotalSupply_ scaledPendingWithdrawals_)
      "OutstandingSupplyUnderflow"

    let reserveProduct_ := mul scaledOutstandingSupply_ reserveRatioBips_
    let reserveNumerator_ ← requireSomeUint
      (safeAdd reserveProduct_ 5000)
      "ReserveRequirementOverflow"
    let scaledReserveRatioRequirement_ := div reserveNumerator_ 10000
    let scaledRequiredLiquidity_ := add scaledReserveRatioRequirement_ scaledPendingWithdrawals_

    let normalizedProduct_ := mul scaledRequiredLiquidity_ scaleFactor_
    let normalizedNumerator_ ← requireSomeUint
      (safeAdd normalizedProduct_ 500000000000000000000000000)
      "NormalizeAmountOverflow"
    let normalizedRequiredLiquidity_ := div normalizedNumerator_ 1000000000000000000000000000

    let liquidityWithFees_ ← requireSomeUint
      (safeAdd normalizedRequiredLiquidity_ updatedAccruedProtocolFees_)
      "LiquidityRequirementOverflow"
    let liquidityRequired_ ← requireSomeUint
      (safeAdd liquidityWithFees_ normalizedUnclaimedWithdrawals_)
      "LiquidityRequirementOverflow"

    let borrowable_ := ite (totalAssets_ > liquidityRequired_) (sub totalAssets_ liquidityRequired_) 0
    require (amount <= borrowable_) "BorrowAmountTooHigh"

    require (hookAllowsBorrow_ != 0) "BorrowHookFailed"

    setStorage totalAssetsStored (sub totalAssets_ amount)
    setStorage accruedProtocolFees updatedAccruedProtocolFees_
    setStorage pendingProtocolFeeDelta 0

end Benchmark.Cases.Wildcat.BorrowLiquiditySafety
