import Benchmark.Cases.Kleros.SortitionTrees.Specs

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity
open Verity.EVM.Uint256

/--
`setLeaf` writes matching forward and reverse mapping entries.
-/
theorem node_id_bijection
    (nodeIndex stakePathID weight : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 7)
    (hHigh : nodeIndex <= 14) :
    let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
    node_id_bijection_spec nodeIndex stakePathID s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Kleros.SortitionTrees
