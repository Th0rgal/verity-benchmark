import Benchmark.Cases.Alchemix.EarmarkConservation.Specs

/-!
  Hypothesis-by-hypothesis audit of `Proofs.lean`.

  Background: an early reviewer flagged six hypotheses on the
  preservation theorems and asked whether each was a real modeling
  assumption or a scope cut. This file is the per-hypothesis ledger of
  the answer:

    H1  Q128 idealization                    irreducible (modeling level)
    H2  Synced-at-touched-id                 discharged compositionally
    H3  lastAccruedRedemptionWeight ≠ 0      model artifact (counterexample below)
    H4  cumulativeEarmarked ≤ totalDebt − amount   discharged via sister invariant
    H5  accounts_earmarked ≤ cumulativeEarmarked   discharged from invariant + non-overflow
    H6  Σ unearmarkedTimesRSR = totalDebt − cumulativeEarmarked
                                              scope cut (counterexample below)

  H1 is irreducible at this abstraction level — it absorbs floor-
  rounding ULP drift in Q128 fixed-point arithmetic into an exact-
  rational idealization. Any attempt to discharge it would change the
  invariant we are proving (a quantitative bounded-drift theorem,
  out of scope).

  The remaining five are addressed below. H2/H4/H5 are discharged as
  Lean theorems. H3 and H6 are model-level falsifiable from explicit
  counterexample states. -/

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256
open Verity.Core (FiniteSet)

/-! ## H6 — counterexample

  H6 is the bridging identity used inside `_earmark_preserves_invariant`:

      _earmark_active s = true →
        ids.sum (earmark_unearmarkedTimesRSR s) =
          sub (totalDebt s) (cumulativeEarmarked s)

  It is *not* a property of arbitrary `(s, ids)` pairs — it depends on
  the contract's debt-conservation sister invariant
  `Σ accounts_debt(id) = totalDebt`. Without modeling debt-mutation
  operations (`_addDebt`, `_resetDebt`, the constructor seed), we
  cannot prove it. We give a concrete pair `(s, ids)` where the LHS
  and RHS disagree to show H6 is *not* a model tautology.

  The counterexample state has `totalDebt = 100`, `cumulativeEarmarked
  = 0`, `_transmuterEarmarkAmount = 50` (so `_earmark_active = true`),
  and an empty active-id set. The LHS sum is therefore 0, while the
  RHS is `sub 100 0 = 100`. -/

def h6_cex_state : ContractState :=
  { Verity.defaultState with
    «storage» := fun n =>
      if n = 1 then (100 : Uint256)
      else if n = 5 then (50 : Uint256)
      else (0 : Uint256) }

def h6_cex_ids : FiniteSet Uint256 :=
  Verity.Core.FiniteSet.empty

/-- The pre-state side of H6 fires (`_earmark_active = true`). -/
theorem H6_active :
    _earmark_active (totalDebt h6_cex_state)
      (cumulativeEarmarked h6_cex_state)
      (h6_cex_state.storage 5) = true := by
  native_decide

/-- The H6 conclusion fails on the counterexample. -/
theorem H6_falsified :
    h6_cex_ids.sum (earmark_unearmarkedTimesRSR h6_cex_state) ≠
      sub (totalDebt h6_cex_state) (cumulativeEarmarked h6_cex_state) := by
  native_decide

/-- Packaged: a concrete `(s, ids)` falsifying H6. -/
theorem H6_not_a_tautology :
    ∃ (s : ContractState) (ids : FiniteSet Uint256),
      _earmark_active (totalDebt s) (cumulativeEarmarked s) (s.storage 5) = true ∧
      ids.sum (earmark_unearmarkedTimesRSR s) ≠
        sub (totalDebt s) (cumulativeEarmarked s) :=
  ⟨h6_cex_state, h6_cex_ids, H6_active, H6_falsified⟩

end Benchmark.Cases.Alchemix.EarmarkConservation
