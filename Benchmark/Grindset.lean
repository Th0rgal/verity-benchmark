import Benchmark.Grindset.Invariants
import Benchmark.Grindset.Reach

/-!
# Benchmark.Grindset — umbrella module

Re-exports the grindset extension modules:
- `Invariants` (A1): 118 `@[grind =] / @[grind →] / @[grind]`-tagged
  invariant lemmas across all benchmark contracts.
- `Reach` (A3): reachability lemma pack and the `verity_reach_grind`
  tactic for `safe/owner_manager_reach` style chain proofs.

Sibling S1 (`grindset/s1-verity-grindset`) contributes `Grindset/Attr.lean`,
`Grindset/Monad.lean`, `Grindset/Core.lean`, and `Grindset/Tests.lean`; those
are imported directly by clients that need them and need not be re-exported
from this umbrella.
-/
