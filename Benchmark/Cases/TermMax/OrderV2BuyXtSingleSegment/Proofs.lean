import Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment

open Verity
open Verity.EVM.Uint256

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
  have hBaseCutBool : cutXtReserve == 0 := by
    simp [hBaseCut]
  cases hNegWord : isNegativeInt256Word cutOffsetWord
  · simp_all [TermMaxOrderV2BuyXtSingleSegment.swapDebtTokenToXtExactInSingleSegment,
      TermMaxOrderV2BuyXtSingleSegment.swapAndUpdateReserves,
      TermMaxOrderV2BuyXtSingleSegment.buyXt,
      TermMaxOrderV2BuyXtSingleSegment.buyToken,
      TermMaxOrderV2BuyXtSingleSegment.buyXtStep,
      TermMaxOrderV2BuyXtSingleSegment.buyXtCurve,
      TermMaxOrderV2BuyXtSingleSegment.cutsReverseIter,
      TermMaxOrderV2BuyXtSingleSegment.calcIntervalProps,
      swapDebtTokenToXt_updates_virtual_xt_reserve_spec,
      singleSegmentBuyXtTokenAmtOut,
      signedReserveOffset,
      singleSegmentScaledLiqSquare,
      isNegativeInt256Word,
      DECIMAL_BASE,
      DAYS_IN_YEAR,
      SIGNED_INT256_BOUND,
      Verity.require,
      Verity.bind,
      Bind.bind,
      Verity.pure,
      Pure.pure,
      Contract.run,
      ContractResult.snd]
    simp [getStorage, setStorage, TermMaxOrderV2BuyXtSingleSegment.virtualXtReserve,
      hSignedOffsetSafe, hVXtNonZero, hNoCross, hMinOut]
  · simp_all [TermMaxOrderV2BuyXtSingleSegment.swapDebtTokenToXtExactInSingleSegment,
      TermMaxOrderV2BuyXtSingleSegment.swapAndUpdateReserves,
      TermMaxOrderV2BuyXtSingleSegment.buyXt,
      TermMaxOrderV2BuyXtSingleSegment.buyToken,
      TermMaxOrderV2BuyXtSingleSegment.buyXtStep,
      TermMaxOrderV2BuyXtSingleSegment.buyXtCurve,
      TermMaxOrderV2BuyXtSingleSegment.cutsReverseIter,
      TermMaxOrderV2BuyXtSingleSegment.calcIntervalProps,
      swapDebtTokenToXt_updates_virtual_xt_reserve_spec,
      singleSegmentBuyXtTokenAmtOut,
      signedReserveOffset,
      singleSegmentScaledLiqSquare,
      isNegativeInt256Word,
      DECIMAL_BASE,
      DAYS_IN_YEAR,
      SIGNED_INT256_BOUND,
      Verity.require,
      Verity.bind,
      Bind.bind,
      Verity.pure,
      Pure.pure,
      Contract.run,
      ContractResult.snd]
    simp [getStorage, setStorage, TermMaxOrderV2BuyXtSingleSegment.virtualXtReserve,
      hSignedOffsetSafe, hVXtNonZero, hNoCross, hMinOut]

end Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment
