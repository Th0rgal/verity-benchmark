import Benchmark.Cases.Alchemix.EarmarkConservation.Specs

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256

/--
Preservation of the lazy-projected earmark conservation invariant under
`earmark()`.

`earmark` increments `cumulativeEarmarked` by `effectiveEarmarked` and
updates `_earmarkWeight` and `_survivalAccumulator`. Every active account's
`projectedEarmarked` increases by an amount that, summed over `ids`,
equals exactly `effectiveEarmarked` (under the Q128-idealization
assumption).
-/
theorem earmark_preserves_invariant
    (s : ContractState)
    (ids : Verity.Core.FiniteSet Uint256) :
    let s' := ((AlchemistEarmark.earmark).run s).snd
    earmark_preserves_invariant_spec s s' ids := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Alchemix.EarmarkConservation
