import Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment

open Verity
open Verity.EVM.Uint256

private theorem uint256_zero_sub_eq_modulus_sub (x : Uint256) :
    sub 0 x = Verity.Core.Uint256.ofNat (Verity.Core.Uint256.modulus - x.val) := by
  cases x with
  | mk val hlt =>
      by_cases h0 : val = 0
      · subst h0
        simp [Verity.EVM.Uint256.sub, Verity.Core.Uint256.sub, Verity.Core.Uint256.ofNat]
      · simp [Verity.EVM.Uint256.sub, Verity.Core.Uint256.sub, Verity.Core.Uint256.ofNat, h0]

private theorem uint256_zero_sub_toUint256_int256 (cutOffset : Int256) :
    sub 0 (Verity.Core.Int256.toUint256 cutOffset) = Verity.Core.Int256.toUint256 (-cutOffset) := by
  rw [uint256_zero_sub_eq_modulus_sub]
  change Verity.Core.Uint256.ofNat (Verity.Core.Uint256.modulus - cutOffset.word.val) =
    (Verity.Core.Int256.ofUint256
      (Verity.Core.Uint256.ofNat (Verity.Core.Int256.modulus - cutOffset.word.val))).word
  rfl

private theorem buyXt_success
    (daysToMaturity debtTokenAmtIn minTokenOut : Uint256)
    (borrowTakerFeeRatio lendMakerFeeRatio : Uint256)
    (cutLiqSquare : Uint256) (cutOffset : Int256)
    (s : ContractState)
    (hNoCross :
      singleSegmentBuyXtTokenAmtOut
          daysToMaturity (s.storage 0) debtTokenAmtIn
          borrowTakerFeeRatio cutLiqSquare cutOffset
        <= s.storage 0)
    (hMinOut :
      add
          (singleSegmentBuyXtTokenAmtOut
            daysToMaturity (s.storage 0) debtTokenAmtIn
            borrowTakerFeeRatio cutLiqSquare cutOffset)
          debtTokenAmtIn
        >= minTokenOut) :
    (TermMaxOrderV2BuyXtSingleSegment.buyXt
      debtTokenAmtIn minTokenOut daysToMaturity
      borrowTakerFeeRatio lendMakerFeeRatio cutLiqSquare cutOffset).run s =
      ContractResult.success
        (add
          (singleSegmentBuyXtTokenAmtOut
            daysToMaturity (s.storage 0) debtTokenAmtIn
            borrowTakerFeeRatio cutLiqSquare cutOffset)
          debtTokenAmtIn,
         sub debtTokenAmtIn
           (div (mul debtTokenAmtIn (sub 100000000 lendMakerFeeRatio))
             (add 100000000 borrowTakerFeeRatio)),
         sub debtTokenAmtIn
           (sub debtTokenAmtIn
             (div (mul debtTokenAmtIn (sub 100000000 lendMakerFeeRatio))
               (add 100000000 borrowTakerFeeRatio))),
         singleSegmentBuyXtTokenAmtOut
           daysToMaturity (s.storage 0) debtTokenAmtIn
           borrowTakerFeeRatio cutLiqSquare cutOffset)
        s := by
  by_cases hNeg : cutOffset < 0
  · simp [TermMaxOrderV2BuyXtSingleSegment.buyXt,
      TermMaxOrderV2BuyXtSingleSegment.buyToken,
      TermMaxOrderV2BuyXtSingleSegment.buyXtStep,
      TermMaxOrderV2BuyXtSingleSegment.buyXtCurve,
      TermMaxOrderV2BuyXtSingleSegment.cutsReverseIter,
      TermMaxOrderV2BuyXtSingleSegment.calcIntervalProps,
      singleSegmentBuyXtTokenAmtOut,
      singleSegmentScaledLiqSquare,
      plusInt256,
      Contracts.requireCustomError,
      Contracts.revertCustomError,
      Verity.bind,
      Bind.bind,
      Verity.pure,
      Pure.pure,
      Contract.run,
      getStorage,
      TermMaxOrderV2BuyXtSingleSegment.virtualXtReserve,
      hNeg,
      uint256_zero_sub_toUint256_int256] at *
    rw [if_pos hNoCross]
    simp [Verity.pure]
    rw [if_pos hMinOut]
    simp [Verity.pure]
  · simp [TermMaxOrderV2BuyXtSingleSegment.buyXt,
      TermMaxOrderV2BuyXtSingleSegment.buyToken,
      TermMaxOrderV2BuyXtSingleSegment.buyXtStep,
      TermMaxOrderV2BuyXtSingleSegment.buyXtCurve,
      TermMaxOrderV2BuyXtSingleSegment.cutsReverseIter,
      TermMaxOrderV2BuyXtSingleSegment.calcIntervalProps,
      singleSegmentBuyXtTokenAmtOut,
      singleSegmentScaledLiqSquare,
      plusInt256,
      Contracts.requireCustomError,
      Contracts.revertCustomError,
      Verity.bind,
      Bind.bind,
      Verity.pure,
      Pure.pure,
      Contract.run,
      getStorage,
      TermMaxOrderV2BuyXtSingleSegment.virtualXtReserve,
      hNeg] at *
    rw [if_pos hNoCross]
    simp [Verity.pure]
    rw [if_pos hMinOut]
    simp [Verity.pure]

/--
Executing the single-segment exact-input `debtToken -> XT` pricing path
updates `virtualXtReserve` (storage slot 0) by exactly the curve-computed
XT output amount.
-/
theorem swapDebtTokenToXt_updates_virtual_xt_reserve
    (daysToMaturity debtTokenAmtIn minTokenOut : Uint256)
    (borrowTakerFeeRatio lendMakerFeeRatio : Uint256)
    (cutLiqSquare : Uint256) (cutOffset : Int256)
    (s : ContractState)
    (hNonZeroInput : debtTokenAmtIn != 0)
    (hLockOpen : s.storage 1 = 0)
    (hVXtNonZero : plusInt256 (s.storage 0) cutOffset != 0)
    (hNoCross :
      singleSegmentBuyXtTokenAmtOut
          daysToMaturity (s.storage 0) debtTokenAmtIn
          borrowTakerFeeRatio cutLiqSquare cutOffset
        <= s.storage 0)
    (hMinOut :
      add
          (singleSegmentBuyXtTokenAmtOut
            daysToMaturity (s.storage 0) debtTokenAmtIn
            borrowTakerFeeRatio cutLiqSquare cutOffset)
          debtTokenAmtIn
        >= minTokenOut) :
    let s' := ((
      TermMaxOrderV2BuyXtSingleSegment.swapDebtTokenToXtExactInSingleSegment
        debtTokenAmtIn minTokenOut daysToMaturity
        borrowTakerFeeRatio lendMakerFeeRatio
        cutLiqSquare cutOffset
      ).run s).snd
    swapDebtTokenToXt_updates_virtual_xt_reserve_spec
      daysToMaturity debtTokenAmtIn
      borrowTakerFeeRatio cutLiqSquare cutOffset
      s s' := by
  let _ := hNonZeroInput
  let _ := hLockOpen
  let _ := hVXtNonZero
  unfold swapDebtTokenToXt_updates_virtual_xt_reserve_spec
  unfold TermMaxOrderV2BuyXtSingleSegment.swapDebtTokenToXtExactInSingleSegment
    TermMaxOrderV2BuyXtSingleSegment.swapAndUpdateReserves
  simp [Verity.bind, Bind.bind, Contract.run]
  have hBuyXt :=
    buyXt_success
      daysToMaturity debtTokenAmtIn minTokenOut
      borrowTakerFeeRatio lendMakerFeeRatio
      cutLiqSquare cutOffset s hNoCross hMinOut
  cases hCall :
      TermMaxOrderV2BuyXtSingleSegment.buyXt
        debtTokenAmtIn minTokenOut daysToMaturity
        borrowTakerFeeRatio lendMakerFeeRatio
        cutLiqSquare cutOffset s
  case success res s1 =>
    have hEq :
        ContractResult.success res s1 =
          ContractResult.success
            (add
              (singleSegmentBuyXtTokenAmtOut
                daysToMaturity (s.storage 0) debtTokenAmtIn
                borrowTakerFeeRatio cutLiqSquare cutOffset)
              debtTokenAmtIn,
             sub debtTokenAmtIn
               (div (mul debtTokenAmtIn (sub 100000000 lendMakerFeeRatio))
                 (add 100000000 borrowTakerFeeRatio)),
             sub debtTokenAmtIn
               (sub debtTokenAmtIn
                 (div (mul debtTokenAmtIn (sub 100000000 lendMakerFeeRatio))
                   (add 100000000 borrowTakerFeeRatio))),
             singleSegmentBuyXtTokenAmtOut
               daysToMaturity (s.storage 0) debtTokenAmtIn
               borrowTakerFeeRatio cutLiqSquare cutOffset)
            s := by
      simpa [Contract.run, hCall] using hBuyXt
    injection hEq with hRes hState
    subst hRes hState
    simp [getStorage, setStorage, Verity.pure, Pure.pure, ContractResult.snd,
      TermMaxOrderV2BuyXtSingleSegment.virtualXtReserve]
  case _ msg s1 =>
    have hImpossible :
        ContractResult.revert msg s1 =
          ContractResult.success
            (add
              (singleSegmentBuyXtTokenAmtOut
                daysToMaturity (s.storage 0) debtTokenAmtIn
                borrowTakerFeeRatio cutLiqSquare cutOffset)
              debtTokenAmtIn,
             sub debtTokenAmtIn
               (div (mul debtTokenAmtIn (sub 100000000 lendMakerFeeRatio))
                 (add 100000000 borrowTakerFeeRatio)),
             sub debtTokenAmtIn
               (sub debtTokenAmtIn
                 (div (mul debtTokenAmtIn (sub 100000000 lendMakerFeeRatio))
                   (add 100000000 borrowTakerFeeRatio))),
             singleSegmentBuyXtTokenAmtOut
               daysToMaturity (s.storage 0) debtTokenAmtIn
               borrowTakerFeeRatio cutLiqSquare cutOffset)
            s := by
      simp [Contract.run, hCall] at hBuyXt
    cases hImpossible

end Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment
