import Benchmark.Cases.Alchemix.EarmarkConservation.Specs

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256

/--
Preservation of the lazy-projected earmark conservation invariant under
`subEarmarkedDebt(amount, accountId)`.

The operation reduces one account's stored `earmarked` by `earmarkToRemove`
and reduces the global by `min(earmarkToRemove, cumulativeEarmarked)`.
Under the invariant pre-state (where the projected sum equals the global),
both decrements coincide.
-/
theorem _subEarmarkedDebt_preserves_invariant
    (s : ContractState)
    (ids : Verity.Core.FiniteSet Uint256)
    (amountInDebtTokens accountId : Uint256) :
    let s' := ((AlchemistV3._subEarmarkedDebt amountInDebtTokens accountId).run s).snd
    _subEarmarkedDebt_preserves_invariant_spec s s' ids accountId := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Alchemix.EarmarkConservation
