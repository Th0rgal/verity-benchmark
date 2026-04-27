import Verity.Specs.Common
import Benchmark.Cases.Wildcat.BorrowLiquiditySafety.Contract

namespace Benchmark.Cases.Wildcat.BorrowLiquiditySafety

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-- Trusted mirror of Wildcat `totalAssets()`. -/
def totalAssetsOf (state : ContractState) : Uint256 := state.storage 0

/-- Encoded `MarketState.isClosed` flag. -/
def isClosedOf (state : ContractState) : Uint256 := state.storage 1

/-- `MarketState.accruedProtocolFees`. -/
def accruedProtocolFeesOf (state : ContractState) : Uint256 := state.storage 2

/-- `MarketState.normalizedUnclaimedWithdrawals`. -/
def normalizedUnclaimedWithdrawalsOf (state : ContractState) : Uint256 := state.storage 3

/-- `MarketState.scaledTotalSupply`. -/
def scaledTotalSupplyOf (state : ContractState) : Uint256 := state.storage 4

/-- `MarketState.scaledPendingWithdrawals`. -/
def scaledPendingWithdrawalsOf (state : ContractState) : Uint256 := state.storage 5

/-- `MarketState.reserveRatioBips`. -/
def reserveRatioBipsOf (state : ContractState) : Uint256 := state.storage 6

/-- `MarketState.scaleFactor`. -/
def scaleFactorOf (state : ContractState) : Uint256 := state.storage 7

/-- Compressed `_getUpdatedState()` fee accrual input. -/
def pendingProtocolFeeDeltaOf (state : ContractState) : Uint256 := state.storage 8

/-- Trusted `_isFlaggedByChainalysis(borrower)` result. -/
def borrowerFlaggedOf (state : ContractState) : Uint256 := state.storage 9

/-- Trusted `hooks.onBorrow` success bit. -/
def hookAllowsBorrowOf (state : ContractState) : Uint256 := state.storage 10

/-- Borrow-check state after the compressed `_getUpdatedState()` fee accrual. -/
def updatedAccruedProtocolFeesOf (preState : ContractState) : Uint256 :=
  accruedProtocolFeesOf preState + pendingProtocolFeeDeltaOf preState

/-- Portion of supply not already pending withdrawal. -/
def scaledOutstandingSupplyOf (preState : ContractState) : Uint256 :=
  outstandingSupply (scaledTotalSupplyOf preState) (scaledPendingWithdrawalsOf preState)

/-- Reserve-ratio-backed outstanding supply plus 100% pending withdrawals. -/
def scaledRequiredReservesOf (preState : ContractState) : Uint256 :=
  bipMulHalfUp (scaledOutstandingSupplyOf preState) (reserveRatioBipsOf preState) +
    scaledPendingWithdrawalsOf preState

/-- Normalized reserve-ratio-backed liquidity requirement. -/
def normalizedRequiredReservesOf (preState : ContractState) : Uint256 :=
  normalizeAmount (scaledRequiredReservesOf preState) (scaleFactorOf preState)

/--
  Required liquidity for the already-updated state used by the borrow guard.

  This includes:
  - reserve-ratio-backed liquidity on non-pending supply
  - pending withdrawals
  - paid but unclaimed withdrawals
  - accrued protocol fees (after the compressed update step)
-/
def requiredLiquidityAfterUpdate (preState : ContractState) : Uint256 :=
  liquidityRequiredFromFields
    (scaledTotalSupplyOf preState)
    (scaledPendingWithdrawalsOf preState)
    (normalizedUnclaimedWithdrawalsOf preState)
    (updatedAccruedProtocolFeesOf preState)
    (reserveRatioBipsOf preState)
    (scaleFactorOf preState)

/-- Borrowable liquidity after the compressed update step. -/
def borrowableAssetsAfterUpdate (preState : ContractState) : Uint256 :=
  borrowableAssetsFromFields
    (totalAssetsOf preState)
    (scaledTotalSupplyOf preState)
    (scaledPendingWithdrawalsOf preState)
    (normalizedUnclaimedWithdrawalsOf preState)
    (updatedAccruedProtocolFeesOf preState)
    (reserveRatioBipsOf preState)
    (scaleFactorOf preState)

/-- Post-state returned by executing the modeled `borrow(amount)` function. -/
def runBorrow (amount : Uint256) (preState : ContractState) : ContractState :=
  ((BorrowLiquiditySafety.borrow amount).run preState).snd

/--
  Preconditions for the successful `borrow(amount)` path in this benchmark slice.

  The arithmetic side conditions mirror the checked-overflow / checked-underflow
  behavior of the Solidity helpers that Wildcat uses while computing the updated
  liquidity requirement.
-/
def borrow_succeeds_preconditions (amount : Uint256) (preState : ContractState) : Prop :=
  borrowerFlaggedOf preState = 0 ∧
  isClosedOf preState = 0 ∧
  hookAllowsBorrowOf preState != 0 ∧
  scaledPendingWithdrawalsOf preState <= scaledTotalSupplyOf preState ∧
  (accruedProtocolFeesOf preState : Nat) + (pendingProtocolFeeDeltaOf preState : Nat) <= MAX_UINT256 ∧
  (scaledOutstandingSupplyOf preState : Nat) * (reserveRatioBipsOf preState : Nat) + (HALF_BIP : Nat)
    <= MAX_UINT256 ∧
  (scaledRequiredReservesOf preState : Nat) * (scaleFactorOf preState : Nat) + (HALF_RAY : Nat)
    <= MAX_UINT256 ∧
  (normalizedRequiredReservesOf preState : Nat) + (updatedAccruedProtocolFeesOf preState : Nat)
    <= MAX_UINT256 ∧
  (normalizedRequiredReservesOf preState : Nat) + (updatedAccruedProtocolFeesOf preState : Nat) +
      (normalizedUnclaimedWithdrawalsOf preState : Nat) <= MAX_UINT256 ∧
  amount <= borrowableAssetsAfterUpdate preState

/--
  Approved invariant: for a successful positive borrow, the market still has at
  least the required liquidity left after the assets leave the contract.
-/
def positive_borrow_preserves_required_liquidity_spec
    (amount : Uint256) (preState postState : ContractState) : Prop :=
  totalAssetsOf postState = totalAssetsOf preState - amount ∧
  totalAssetsOf postState >= requiredLiquidityAfterUpdate preState

end Benchmark.Cases.Wildcat.BorrowLiquiditySafety
