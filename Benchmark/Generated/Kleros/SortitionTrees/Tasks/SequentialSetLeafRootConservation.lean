import Benchmark.Cases.Kleros.SortitionTrees.Specs

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity
open Verity.EVM.Uint256

/--
After two consecutive `setLeaf` calls, the root still equals the sum of all leaves.
This proves the conservation invariant is inductive.
-/
theorem sequential_setLeaf_root_conservation
    (idx1 id1 w1 idx2 id2 w2 : Uint256) (s : ContractState)
    (_hLow1 : idx1 >= 7) (_hHigh1 : idx1 <= 14)
    (hLow2 : idx2 >= 7) (hHigh2 : idx2 <= 14) :
    let s'  := ((SortitionTrees.setLeaf idx1 id1 w1).run s).snd
    let s'' := ((SortitionTrees.setLeaf idx2 id2 w2).run s').snd
    sequential_setLeaf_root_conservation_spec s'' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Kleros.SortitionTrees
