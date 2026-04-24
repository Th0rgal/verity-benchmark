import Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment

open Verity
open Verity.EVM.Uint256

/--
Executing the single-segment exact-input `debtToken -> XT` pricing path
updates `virtualXtReserve` (storage slot 0) by exactly the curve-computed
XT output amount.

NOTE: this proof is currently a `sorry` placeholder while the contract is
being refactored to a higher-fidelity Solidity-shaped form (use of
`Int256` for the curve offset, named errors, `nonreentrant` modifier).
The previous `simp_all` proof in this file no longer applies because the
contract surface has changed:

- `cutOffsetWord : Uint256` is now `cutOffset : Int256`, so the proof must
  reason via `Int256.isNeg` / `Int256.neg` / `toUint256` instead of the
  removed `signedReserveOffset` / `isNegativeInt256Word`.
- `requireError ... InsufficientLiquidity()` and
  `requireError ... UnexpectedAmount(_, _)` replace the previous
  `require ... "string"` calls.
- The function takes the `nonreentrant(nonReentrancyLock)` modifier, so
  the call now reads/writes `s.storage 1` in addition to `s.storage 0`.
- The storage read of `virtualXtReserve` now happens inside `buyToken`
  (mirroring Solidity `_buyToken` line 1093) rather than being threaded
  in from `swapAndUpdateReserves`.

A separate proof-engineering pass will discharge the `sorry` below using
the standard `simp_all` unfolding pattern from PR #31, extended with the
new function-name unfolds and `Int256` lemmas.
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
  sorry

end Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment
