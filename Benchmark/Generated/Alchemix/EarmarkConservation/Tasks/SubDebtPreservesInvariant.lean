import Benchmark.Cases.Alchemix.EarmarkConservation.Specs

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256

/--
Preservation of the lazy-projected earmark conservation invariant under
`subDebt(tokenId, amount)`.

The operation decrements `totalDebt` and clamps `cumulativeEarmarked`
down to the new `totalDebt` if necessary. Under the invariant pre-state
together with `cumulativeEarmarked ≤ totalDebt` (a corollary of the
invariant that always holds), the clamp is a no-op and conservation is
preserved trivially.
-/
theorem _subDebt_preserves_invariant
    (s : ContractState)
    (ids : Verity.Core.FiniteSet Uint256)
    (tokenId amount : Uint256) :
    let s' := ((AlchemistV3._subDebt tokenId amount).run s).snd
    _subDebt_preserves_invariant_spec s s' ids tokenId := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Alchemix.EarmarkConservation
