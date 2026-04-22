import Benchmark.Cases.Wildcat.BorrowLiquiditySafety.Specs

namespace Benchmark.Cases.Wildcat.BorrowLiquiditySafety

open Verity
open Verity.EVM.Uint256

/--
Executing a successful positive `borrow(amount)` leaves at least the required
liquidity in the market after the transfer.
-/
theorem positive_borrow_preserves_required_liquidity
    (amount : Uint256) (s : ContractState)
    (hPositive : amount > 0)
    (hPre : borrow_succeeds_preconditions amount s) :
    let s' := ((BorrowLiquiditySafety.borrow amount).run s).snd
    positive_borrow_preserves_required_liquidity_spec amount s s' := by
  exact ?_

end Benchmark.Cases.Wildcat.BorrowLiquiditySafety
