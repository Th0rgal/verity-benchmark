/-
  Benchmark.Grindset — minimal stub so generated task skeletons that
  `import Benchmark.Grindset` still build when the real grindset lemma
  bundle has not landed yet.

  The real module is developed on branch `grindset/s1-verity-grindset`.
  When that branch lands, this file should be replaced by the actual
  bundle of `@[grind]`-tagged operational lemmas for Verity execution
  (getStorage / setStorage / getMapping / setMapping / Verity.require /
   Verity.bind / Contract.run / ContractResult.snd / ... ).

  Until then this stub:
    * exists so `import Benchmark.Grindset` resolves,
    * defines nothing that could conflict with the real bundle,
    * does not re-export or `open` anything that could shadow case symbols.

  Keep this file content-free on purpose. DO NOT add lemmas here; they
  belong in the s1 branch.
-/

namespace Benchmark.Grindset

-- intentionally empty

end Benchmark.Grindset
