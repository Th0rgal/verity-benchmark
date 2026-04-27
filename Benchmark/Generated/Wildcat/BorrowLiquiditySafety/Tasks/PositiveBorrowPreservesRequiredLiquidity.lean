import Benchmark.Cases.Wildcat.BorrowLiquiditySafety.Proofs

namespace Benchmark.Cases.Wildcat.BorrowLiquiditySafety

open Verity
open Verity.EVM.Uint256

/--
Executing a successful positive `borrow(amount)` leaves at least the required
liquidity in the market after the transfer.
-/
theorem positive_borrow_preserves_required_liquidity
    (amount : Uint256) (preState : ContractState)
    (hPositive : amount > 0)
    (hPre : borrow_succeeds_preconditions amount preState) :
    let postState := runBorrow amount preState;
    positive_borrow_preserves_required_liquidity_spec amount preState postState := by
  exact
    Benchmark.Cases.Wildcat.BorrowLiquiditySafety.positive_borrow_preserves_required_liquidity
      amount preState hPositive hPre

end Benchmark.Cases.Wildcat.BorrowLiquiditySafety
