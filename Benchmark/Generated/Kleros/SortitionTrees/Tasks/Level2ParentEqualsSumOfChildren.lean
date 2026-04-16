import Benchmark.Cases.Kleros.SortitionTrees.Specs

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity
open Verity.EVM.Uint256

/--
After `setLeaf`, each level-2 node equals the sum of its two leaf children.
-/
theorem level2_parent_equals_sum_of_children
    (nodeIndex stakePathID weight : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 7)
    (hHigh : nodeIndex <= 14) :
    let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
    level2_parent_equals_sum_of_children_spec s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Kleros.SortitionTrees
