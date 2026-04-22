import Verity.Specs.Common
import Benchmark.Cases.Wildcat.BorrowLiquiditySafety.Contract

namespace Benchmark.Cases.Wildcat.BorrowLiquiditySafety

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-- Trusted mirror of Wildcat `totalAssets()`. -/
def totalAssetsOf (s : ContractState) : Uint256 := s.storage 0

/-- Encoded `MarketState.isClosed` flag. -/
def isClosedOf (s : ContractState) : Uint256 := s.storage 1

/-- `MarketState.accruedProtocolFees`. -/
def accruedProtocolFeesOf (s : ContractState) : Uint256 := s.storage 2

/-- `MarketState.normalizedUnclaimedWithdrawals`. -/
def normalizedUnclaimedWithdrawalsOf (s : ContractState) : Uint256 := s.storage 3

/-- `MarketState.scaledTotalSupply`. -/
def scaledTotalSupplyOf (s : ContractState) : Uint256 := s.storage 4

/-- `MarketState.scaledPendingWithdrawals`. -/
def scaledPendingWithdrawalsOf (s : ContractState) : Uint256 := s.storage 5

/-- `MarketState.reserveRatioBips`. -/
def reserveRatioBipsOf (s : ContractState) : Uint256 := s.storage 6

/-- `MarketState.scaleFactor`. -/
def scaleFactorOf (s : ContractState) : Uint256 := s.storage 7

/-- Compressed `_getUpdatedState()` fee accrual input. -/
def pendingProtocolFeeDeltaOf (s : ContractState) : Uint256 := s.storage 8

/-- Trusted `_isFlaggedByChainalysis(borrower)` result. -/
def borrowerFlaggedOf (s : ContractState) : Uint256 := s.storage 9

/-- Trusted `hooks.onBorrow` success bit. -/
def hookAllowsBorrowOf (s : ContractState) : Uint256 := s.storage 10

/-- Borrow-check state after the compressed `_getUpdatedState()` fee accrual. -/
def updatedAccruedProtocolFeesOf (s : ContractState) : Uint256 :=
  accruedProtocolFeesOf s + pendingProtocolFeeDeltaOf s

/-- Portion of supply not already pending withdrawal. -/
def scaledOutstandingSupplyOf (s : ContractState) : Uint256 :=
  outstandingSupply (scaledTotalSupplyOf s) (scaledPendingWithdrawalsOf s)

/-- Reserve-ratio-backed outstanding supply plus 100% pending withdrawals. -/
def scaledRequiredReservesOf (s : ContractState) : Uint256 :=
  bipMulHalfUp (scaledOutstandingSupplyOf s) (reserveRatioBipsOf s) +
    scaledPendingWithdrawalsOf s

/-- Normalized reserve-ratio-backed liquidity requirement. -/
def normalizedRequiredReservesOf (s : ContractState) : Uint256 :=
  normalizeAmount (scaledRequiredReservesOf s) (scaleFactorOf s)

/--
  Required liquidity for the already-updated state used by the borrow guard.

  This includes:
  - reserve-ratio-backed liquidity on non-pending supply
  - pending withdrawals
  - paid but unclaimed withdrawals
  - accrued protocol fees (after the compressed update step)
-/
def requiredLiquidityAfterUpdate (s : ContractState) : Uint256 :=
  liquidityRequiredFromFields
    (scaledTotalSupplyOf s)
    (scaledPendingWithdrawalsOf s)
    (normalizedUnclaimedWithdrawalsOf s)
    (updatedAccruedProtocolFeesOf s)
    (reserveRatioBipsOf s)
    (scaleFactorOf s)

/-- Borrowable liquidity after the compressed update step. -/
def borrowableAssetsAfterUpdate (s : ContractState) : Uint256 :=
  borrowableAssetsFromFields
    (totalAssetsOf s)
    (scaledTotalSupplyOf s)
    (scaledPendingWithdrawalsOf s)
    (normalizedUnclaimedWithdrawalsOf s)
    (updatedAccruedProtocolFeesOf s)
    (reserveRatioBipsOf s)
    (scaleFactorOf s)

/--
  Preconditions for the successful `borrow(amount)` path in this benchmark slice.

  The arithmetic side conditions mirror the checked-overflow / checked-underflow
  behavior of the Solidity helpers that Wildcat uses while computing the updated
  liquidity requirement.
-/
def borrow_succeeds_preconditions (amount : Uint256) (s : ContractState) : Prop :=
  borrowerFlaggedOf s = 0 ∧
  isClosedOf s = 0 ∧
  hookAllowsBorrowOf s != 0 ∧
  scaledPendingWithdrawalsOf s <= scaledTotalSupplyOf s ∧
  (accruedProtocolFeesOf s : Nat) + (pendingProtocolFeeDeltaOf s : Nat) <= MAX_UINT256 ∧
  (scaledOutstandingSupplyOf s : Nat) * (reserveRatioBipsOf s : Nat) + (HALF_BIP : Nat)
    <= MAX_UINT256 ∧
  (scaledRequiredReservesOf s : Nat) * (scaleFactorOf s : Nat) + (HALF_RAY : Nat)
    <= MAX_UINT256 ∧
  (normalizedRequiredReservesOf s : Nat) + (updatedAccruedProtocolFeesOf s : Nat)
    <= MAX_UINT256 ∧
  (normalizedRequiredReservesOf s : Nat) + (updatedAccruedProtocolFeesOf s : Nat) +
      (normalizedUnclaimedWithdrawalsOf s : Nat) <= MAX_UINT256 ∧
  amount <= borrowableAssetsAfterUpdate s

/--
  Approved invariant: for a successful positive borrow, the market still has at
  least the required liquidity left after the assets leave the contract.
-/
def positive_borrow_preserves_required_liquidity_spec
    (amount : Uint256) (s s' : ContractState) : Prop :=
  totalAssetsOf s' = totalAssetsOf s - amount ∧
  totalAssetsOf s' >= requiredLiquidityAfterUpdate s

end Benchmark.Cases.Wildcat.BorrowLiquiditySafety
