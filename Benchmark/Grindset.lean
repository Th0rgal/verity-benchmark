/-
  Benchmark.Grindset

  Minimal stub created by worker A1 (branch `grindset/a1-invariant-tags`).
  Sibling worker S1 (`grindset/s1-verity-grindset`) owns this module and will replace/extend it
  with their operational-primitives tagging. For now, this stub only re-exports A1's invariant
  tags so that `lake build Benchmark.Grindset` is not broken on branches that touch it.
-/

import Benchmark.Grindset.Invariants
