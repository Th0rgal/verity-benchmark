import Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.Specs

namespace Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment

open Verity
open Verity.EVM.Uint256

/--
Executing the single-segment exact-input `debtToken -> XT` pricing path updates
`virtualXtReserve` by exactly the curve-computed XT output amount.
-/
theorem swapDebtTokenToXt_updates_virtual_xt_reserve
    (daysToMaturity debtTokenAmtIn minTokenOut : Uint256)
    (borrowTakerFeeRatio lendMakerFeeRatio : Uint256)
    (cutXtReserve cutLiqSquare cutOffsetWord : Uint256)
    (s : ContractState)
    (hNonZeroInput : debtTokenAmtIn != 0)
    (hBaseCut : cutXtReserve = 0)
    (hSignedOffsetSafe :
      if isNegativeInt256Word cutOffsetWord then
        sub 0 cutOffsetWord <= s.storage 0
      else
        add (s.storage 0) cutOffsetWord >= s.storage 0)
    (hVXtNonZero : signedReserveOffset (s.storage 0) cutOffsetWord != 0)
    (hNoCross :
      singleSegmentBuyXtTokenAmtOut
          daysToMaturity
          (s.storage 0)
          debtTokenAmtIn
          borrowTakerFeeRatio
          cutLiqSquare
          cutOffsetWord
        <= s.storage 0)
    (hMinOut :
      add
          (singleSegmentBuyXtTokenAmtOut
            daysToMaturity
            (s.storage 0)
            debtTokenAmtIn
            borrowTakerFeeRatio
            cutLiqSquare
            cutOffsetWord)
          debtTokenAmtIn
        >= minTokenOut) :
    let s' := ((
      TermMaxOrderV2BuyXtSingleSegment.swapDebtTokenToXtExactInSingleSegment
        daysToMaturity
        debtTokenAmtIn
        minTokenOut
        borrowTakerFeeRatio
        lendMakerFeeRatio
        cutXtReserve
        cutLiqSquare
        cutOffsetWord
      ).run s).snd
    swapDebtTokenToXt_updates_virtual_xt_reserve_spec
      daysToMaturity
      debtTokenAmtIn
      borrowTakerFeeRatio
      cutLiqSquare
      cutOffsetWord
      s
      s' := by
  exact ?_

end Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment
