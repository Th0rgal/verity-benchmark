import Verity.Specs.Common
import Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.Contract

namespace Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment

open Verity
open Verity.EVM.Uint256

def swapDebtTokenToXt_updates_virtual_xt_reserve_spec
    (daysToMaturity debtTokenAmtIn : Uint256)
    (borrowTakerFeeRatio cutLiqSquare cutOffsetWord : Uint256)
    (s s' : ContractState) : Prop :=
  s'.storage 0 =
    sub (s.storage 0)
      (singleSegmentBuyXtTokenAmtOut
        daysToMaturity
        (s.storage 0)
        debtTokenAmtIn
        borrowTakerFeeRatio
        cutLiqSquare
        cutOffsetWord)

end Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment
