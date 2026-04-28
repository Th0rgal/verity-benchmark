import Verity.Specs.Common
import Benchmark.Cases.Cork.PoolSolvency.Contract

namespace Benchmark.Cases.Cork.PoolSolvency

open Verity
open Verity.EVM.Uint256

/-
  Specifications for the Cork Pool solvency invariant (Certora P-02).

  P-02: Before a market's expiry, locked collateral normalized to 18 decimals
  must cover the outstanding swap share supply:

    collateralAssetLocked * colScaleUp >= swapTotalSupply - swapBalanceOfPool

  This property was verified by Certora for all CorkPool functions except
  unwindExerciseOther (timeout). This spec targets that gap.

  Storage layout (from verity_contract CorkUnwindExerciseOther):
    slot 0: collateralAssetLocked (collateral-native decimals)
    slot 1: swapTotalSupply (18 decimals, unchanged)
    slot 2: swapBalanceOfPool (18 decimals)
    slot 3: swapRate (18 decimals, unchanged)
    slot 4: refScaleUp (unchanged)
    slot 5: colScaleUp (unchanged)
-/

/--
  P-02 solvency invariant for unwindExerciseOther.
  After executing unwindExerciseOther, collateralAssetLocked (slot 0)
  multiplied by colScaleUp (slot 5) must be at least the outstanding
  swap shares: swapTotalSupply (slot 1) minus swapBalanceOfPool (slot 2).

  collateralAssetLocked' * colScaleUp >= swapTotalSupply - swapBalanceOfPool'
-/
def solvency_preserved_spec
    (_s s' : ContractState) : Prop :=
  mul (s'.storage 0) (s'.storage 5) ≥ sub (s'.storage 1) (s'.storage 2)

end Benchmark.Cases.Cork.PoolSolvency
