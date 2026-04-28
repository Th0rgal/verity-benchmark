import Benchmark.Cases.Alchemix.EarmarkConservation.Specs

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256

/--
Preservation of the lazy-projected earmark conservation invariant under
`syncAccount(id)`.

`syncAccount` writes one account's projected values into storage and
advances its weight snapshots. The projected sum is unchanged because
syncing replaces the stored value with what the projection already
returned at the current global weights.
-/
theorem syncAccount_preserves_invariant
    (s : ContractState)
    (ids : Verity.Core.FiniteSet Uint256)
    (tokenId : Uint256) :
    let s' := ((AlchemistEarmark.syncAccount tokenId).run s).snd
    syncAccount_preserves_invariant_spec s s' ids := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Alchemix.EarmarkConservation
