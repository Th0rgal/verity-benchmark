import Verity.Specs.Common
import Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.Contract

namespace Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment

open Verity
open Verity.EVM.Uint256

/--
Successful execution of the modeled single-segment exact-input
`debtToken -> XT` path leaves `virtualXtReserve` (storage slot 0) decreased
by exactly the curve-computed XT output amount.

`s.storage 1` (the `nonReentrancyLock`) is unconstrained by this spec.
-/
def swapDebtTokenToXt_updates_virtual_xt_reserve_spec
    (daysToMaturity debtTokenAmtIn : Uint256)
    (borrowTakerFeeRatio cutLiqSquare : Uint256)
    (cutOffset : Int256)
    (s s' : ContractState) : Prop :=
  s'.storage 0 =
    sub (s.storage 0)
      (singleSegmentBuyXtTokenAmtOut
        daysToMaturity (s.storage 0) debtTokenAmtIn
        borrowTakerFeeRatio cutLiqSquare cutOffset)

end Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment
