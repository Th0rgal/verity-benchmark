import Benchmark.Cases.Alchemix.EarmarkConservation.Specs
import Benchmark.Cases.Alchemix.EarmarkConservation.Contract

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

/-! ## H3 — counterexample

  H3 is the precondition `∀ id ∈ ids, accounts_lastAccruedRedemptionWeight
  s id ≠ 0` carried by `redeem_preserves_invariant`. We show it cannot
  be dropped: a state satisfying the conservation invariant in pre, and
  violating H3, can have the conservation invariant break in post-state
  after `redeem(amount)`.

  Storage layout of the witness (as in the `Proofs.lean` H3 commentary):
    storage 0  (cumulativeEarmarked)         = 2
    storage 1  (totalDebt)                   = 3
    storage 2  (_earmarkWeight)              = ONE_Q128
    storage 3  (_redemptionWeight)           = 0   ← witness of ¬H3 globally
    storageMapUint 100 1 (debt)              = 3
    storageMapUint 101 1 (earmarked)         = 2
    storageMapUint 102 1 (lastAccruedEW)     = ONE_Q128
    storageMapUint 103 1 (lastAccruedRW)     = 0   ← H3 violated
    ids = {1}.

  The post-state (after `redeem(1)`) has cumulativeEarmarked = 1 but
  the per-account projection still computes to 2 because both the
  pre and post `_redemptionWeight` and `lastAccruedRedemptionWeight`
  are zero, so the redemption survival ratio collapses to ONE_Q128
  via the `lastRW = rW` branch — the projection ignores the redeem
  step entirely. -/

def h3_cex_state : ContractState :=
  { Verity.defaultState with
    «storage» := fun n =>
      if n = 0 then (2 : Uint256)
      else if n = 1 then (3 : Uint256)
      else if n = 2 then ONE_Q128
      else (0 : Uint256)
    «storageMapUint» := fun n k =>
      if n = 100 ∧ k = (1 : Uint256) then (3 : Uint256)
      else if n = 101 ∧ k = (1 : Uint256) then (2 : Uint256)
      else if n = 102 ∧ k = (1 : Uint256) then ONE_Q128
      else (0 : Uint256) }

def h3_cex_ids : FiniteSet Uint256 :=
  ⟨[(1 : Uint256)], by simp⟩

/-- The conservation invariant holds in the pre-state. -/
theorem H3_pre_invariant :
    sumProjectedEarmarked h3_cex_state h3_cex_ids =
      cumulativeEarmarked h3_cex_state := by
  native_decide

/-- H3 is violated in the pre-state: the lastAccruedRedemptionWeight
    snapshot at the active id is zero. -/
theorem H3_violated :
    accounts_lastAccruedRedemptionWeight h3_cex_state (1 : Uint256) = 0 := by
  native_decide

/-- The conservation invariant *fails* in the post-state after
    `redeem(1)` — even though the pre-state satisfied it. The
    failure is caused by the lastRW = 0 condition that H3 was
    designed to rule out. -/
theorem H3_post_invariant_fails :
    let s' := ((AlchemistV3.redeem 1).run h3_cex_state).snd
    sumProjectedEarmarked s' h3_cex_ids ≠ cumulativeEarmarked s' := by
  native_decide

/-- Packaged: a concrete state where the conservation invariant
    holds, H3 fails, and `redeem` breaks the invariant. This shows
    H3 cannot be dropped from `redeem_preserves_invariant`. -/
theorem H3_required_for_redeem :
    ∃ (s : ContractState) (ids : FiniteSet Uint256) (id : Uint256) (amount : Uint256),
      id ∈ ids.elements ∧
      accounts_lastAccruedRedemptionWeight s id = 0 ∧
      sumProjectedEarmarked s ids = cumulativeEarmarked s ∧
      let s' := ((AlchemistV3.redeem amount).run s).snd
      sumProjectedEarmarked s' ids ≠ cumulativeEarmarked s' := by
  refine ⟨h3_cex_state, h3_cex_ids, (1 : Uint256), (1 : Uint256), ?_, ?_, ?_, ?_⟩
  · -- 1 ∈ {1}.elements
    show (1 : Uint256) ∈ [(1 : Uint256)]
    simp
  · exact H3_violated
  · exact H3_pre_invariant
  · exact H3_post_invariant_fails

end Benchmark.Cases.Alchemix.EarmarkConservation
