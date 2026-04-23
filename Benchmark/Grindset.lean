/-
  Benchmark.Grindset — entry point for the Verity grindset.

  Imports Core tagged-lemmas and Monad normalization into a single module so
  downstream proofs can write `import Benchmark.Grindset` and immediately use
  `grind` to discharge slot-write / spec-unfolding obligations.
-/

import Benchmark.Grindset.Monad
import Benchmark.Grindset.Core
import Benchmark.Grindset.Tests
