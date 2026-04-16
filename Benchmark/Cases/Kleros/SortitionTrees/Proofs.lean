import Benchmark.Cases.Kleros.SortitionTrees.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity
open Verity.EVM.Uint256

/-! ### Simp lemma list shared across most proofs -/

private abbrev storageSimpLemmas := [
  ``SortitionTrees.rootSum, ``SortitionTrees.node1, ``SortitionTrees.node2,
  ``SortitionTrees.node3, ``SortitionTrees.node4, ``SortitionTrees.node5,
  ``SortitionTrees.node6,
  ``SortitionTrees.leaf0, ``SortitionTrees.leaf1, ``SortitionTrees.leaf2,
  ``SortitionTrees.leaf3, ``SortitionTrees.leaf4, ``SortitionTrees.leaf5,
  ``SortitionTrees.leaf6, ``SortitionTrees.leaf7,
  ``SortitionTrees.nodeIndexesToIDs, ``SortitionTrees.IDsToNodeIndexes,
  ``SortitionTrees.selectedNode,
  ``getStorage, ``setStorage, ``getMappingUint, ``setMappingUint,
  ``Verity.require, ``Verity.bind, ``Bind.bind, ``Verity.pure, ``Pure.pure,
  ``Contract.run, ``ContractResult.snd]

/-! ### Helper: draw semantics -/

private theorem draw_selected_node
    (ticket : Uint256) (s : ContractState)
    (hRoot : s.storage 0 != 0)
    (hInRange : ticket < s.storage 0) :
    let s' := ((SortitionTrees.draw ticket).run s).snd
    s'.storage 17 =
      ite (ticket < s.storage 1)
        (ite (ticket < s.storage 3)
          (ite (ticket < s.storage 7) 7 8)
          (ite (sub ticket (s.storage 3) < s.storage 9) 9 10))
        (ite (sub ticket (s.storage 1) < s.storage 5)
          (ite (sub ticket (s.storage 1) < s.storage 11) 11 12)
          (ite (sub (sub ticket (s.storage 1)) (s.storage 5) < s.storage 13) 13 14)) := by
  have hRoot' : ¬ s.storage 0 = 0 := by
    intro hEq
    simp [hEq] at hRoot
  simp [SortitionTrees.draw, SortitionTrees.rootSum, SortitionTrees.node1,
    SortitionTrees.node3, SortitionTrees.node5,
    SortitionTrees.leaf0, SortitionTrees.leaf2, SortitionTrees.leaf4, SortitionTrees.leaf6,
    SortitionTrees.selectedNode, hRoot', hInRange, getStorage, setStorage,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd]

/-! ### Exhaustive case-split macro for 8 leaf indices -/

/-- Helper to discharge the impossible case when nodeIndex ∈ [7..14] is exhausted. -/
private theorem leaf_index_exhausted
    (nodeIndex : Uint256)
    (hLow : nodeIndex >= 7) (hHigh : nodeIndex <= 14)
    (h7 : ¬(nodeIndex == 7)) (h8 : ¬(nodeIndex == 8))
    (h9 : ¬(nodeIndex == 9)) (h10 : ¬(nodeIndex == 10))
    (h11 : ¬(nodeIndex == 11)) (h12 : ¬(nodeIndex == 12))
    (h13 : ¬(nodeIndex == 13)) (h14 : ¬(nodeIndex == 14)) : False := by
  have hLow' : (7 : Nat) ≤ nodeIndex.val := by simpa using hLow
  have hHigh' : nodeIndex.val ≤ 14 := by simpa using hHigh
  have := fun (n : Uint256) (h : ¬(nodeIndex == n)) => by simpa using h
  have h7' := this 7 h7; have h8' := this 8 h8
  have h9' := this 9 h9; have h10' := this 10 h10
  have h11' := this 11 h11; have h12' := this 12 h12
  have h13' := this 13 h13; have h14' := this 14 h14
  have h7v : nodeIndex.val ≠ 7 := by intro hv; exact h7' (Verity.Core.Uint256.ext hv)
  have h8v : nodeIndex.val ≠ 8 := by intro hv; exact h8' (Verity.Core.Uint256.ext hv)
  have h9v : nodeIndex.val ≠ 9 := by intro hv; exact h9' (Verity.Core.Uint256.ext hv)
  have h10v : nodeIndex.val ≠ 10 := by intro hv; exact h10' (Verity.Core.Uint256.ext hv)
  have h11v : nodeIndex.val ≠ 11 := by intro hv; exact h11' (Verity.Core.Uint256.ext hv)
  have h12v : nodeIndex.val ≠ 12 := by intro hv; exact h12' (Verity.Core.Uint256.ext hv)
  have h13v : nodeIndex.val ≠ 13 := by intro hv; exact h13' (Verity.Core.Uint256.ext hv)
  have h14v : nodeIndex.val ≠ 14 := by intro hv; exact h14' (Verity.Core.Uint256.ext hv)
  omega

private theorem nat_sum_lt_modulus_of_le_max
    (a b : Uint256)
    (h : (a : Nat) + (b : Nat) ≤ Verity.Core.MAX_UINT256) :
    (a : Nat) + (b : Nat) < Verity.Core.Uint256.modulus := by
  have h' : (a : Nat) + (b : Nat) < Verity.Core.MAX_UINT256 + 1 := Nat.lt_succ_of_le h
  simpa [Verity.Core.Uint256.max_uint256_succ_eq_modulus] using h'

private theorem eq_add_val_of_no_wrap
    {lhs a b : Uint256}
    (hEq : lhs = add a b)
    (hNoWrap : (a : Nat) + (b : Nat) ≤ Verity.Core.MAX_UINT256) :
    (lhs : Nat) = (a : Nat) + (b : Nat) := by
  rw [hEq]
  exact Verity.EVM.Uint256.add_eq_of_lt (nat_sum_lt_modulus_of_le_max a b hNoWrap)

private theorem ge_left_of_eq_add_no_wrap
    {lhs a b : Uint256}
    (hEq : lhs = add a b)
    (hNoWrap : (a : Nat) + (b : Nat) ≤ Verity.Core.MAX_UINT256) :
    lhs >= a := by
  have hVal : (lhs : Nat) = (a : Nat) + (b : Nat) := eq_add_val_of_no_wrap hEq hNoWrap
  simp [hVal]

private theorem ge_right_of_eq_add_no_wrap
    {lhs a b : Uint256}
    (hEq : lhs = add a b)
    (hNoWrap : (a : Nat) + (b : Nat) ≤ Verity.Core.MAX_UINT256) :
    lhs >= b := by
  have hVal : (lhs : Nat) = (a : Nat) + (b : Nat) := eq_add_val_of_no_wrap hEq hNoWrap
  simp [hVal]

/-! ### Level-2 parent equals sum of children -/

/--
After `setLeaf`, each level-2 node equals the sum of its two leaf children.
-/
theorem level2_parent_equals_sum_of_children
    (nodeIndex stakePathID weight : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 7)
    (hHigh : nodeIndex <= 14) :
    let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
    level2_parent_equals_sum_of_children_spec s' := by
  by_cases h7 : nodeIndex == 7
  · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, level2_parent_equals_sum_of_children_spec,
      SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
      SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
      SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
      SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
      SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
      getStorage, setStorage, setMappingUint, Verity.require,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
  · by_cases h8 : nodeIndex == 8
    · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, level2_parent_equals_sum_of_children_spec,
        SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
        SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
        SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
        SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
        SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
        getStorage, setStorage, setMappingUint, Verity.require,
        Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
    · by_cases h9 : nodeIndex == 9
      · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, level2_parent_equals_sum_of_children_spec,
          SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
          SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
          SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
          SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
          SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
          getStorage, setStorage, setMappingUint, Verity.require,
          Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
      · by_cases h10 : nodeIndex == 10
        · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, level2_parent_equals_sum_of_children_spec,
            SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
            SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
            SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
            SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
            SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
            getStorage, setStorage, setMappingUint, Verity.require,
            Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
        · by_cases h11 : nodeIndex == 11
          · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, h11, level2_parent_equals_sum_of_children_spec,
              SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
              SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
              SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
              SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
              SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
              getStorage, setStorage, setMappingUint, Verity.require,
              Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
          · by_cases h12 : nodeIndex == 12
            · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, h11, h12, level2_parent_equals_sum_of_children_spec,
                SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
                SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
                SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
                SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
                SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
                getStorage, setStorage, setMappingUint, Verity.require,
                Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
            · by_cases h13 : nodeIndex == 13
              · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, h11, h12, h13, level2_parent_equals_sum_of_children_spec,
                  SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
                  SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
                  SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
                  SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
                  SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
                  getStorage, setStorage, setMappingUint, Verity.require,
                  Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
              · by_cases h14 : nodeIndex == 14
                · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, h11, h12, h13, h14, level2_parent_equals_sum_of_children_spec,
                    SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
                    SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
                    SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
                    SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
                    SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
                    getStorage, setStorage, setMappingUint, Verity.require,
                    Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
                · exfalso; exact leaf_index_exhausted nodeIndex hLow hHigh h7 h8 h9 h10 h11 h12 h13 h14

/-! ### Level-1 parent equals sum of children -/

/--
After `setLeaf`, each level-1 node equals the sum of its two level-2 children.
-/
theorem level1_parent_equals_sum_of_children
    (nodeIndex stakePathID weight : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 7)
    (hHigh : nodeIndex <= 14) :
    let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
    level1_parent_equals_sum_of_children_spec s' := by
  by_cases h7 : nodeIndex == 7
  · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, level1_parent_equals_sum_of_children_spec,
      SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
      SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
      SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
      SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
      SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
      getStorage, setStorage, setMappingUint, Verity.require,
      Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
  · by_cases h8 : nodeIndex == 8
    · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, level1_parent_equals_sum_of_children_spec,
        SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
        SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
        SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
        SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
        SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
        getStorage, setStorage, setMappingUint, Verity.require,
        Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
    · by_cases h9 : nodeIndex == 9
      · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, level1_parent_equals_sum_of_children_spec,
          SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
          SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
          SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
          SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
          SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
          getStorage, setStorage, setMappingUint, Verity.require,
          Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
      · by_cases h10 : nodeIndex == 10
        · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, level1_parent_equals_sum_of_children_spec,
            SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
            SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
            SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
            SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
            SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
            getStorage, setStorage, setMappingUint, Verity.require,
            Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
        · by_cases h11 : nodeIndex == 11
          · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, h11, level1_parent_equals_sum_of_children_spec,
              SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
              SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
              SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
              SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
              SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
              getStorage, setStorage, setMappingUint, Verity.require,
              Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
          · by_cases h12 : nodeIndex == 12
            · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, h11, h12, level1_parent_equals_sum_of_children_spec,
                SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
                SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
                SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
                SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
                SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
                getStorage, setStorage, setMappingUint, Verity.require,
                Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
            · by_cases h13 : nodeIndex == 13
              · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, h11, h12, h13, level1_parent_equals_sum_of_children_spec,
                  SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
                  SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
                  SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
                  SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
                  SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
                  getStorage, setStorage, setMappingUint, Verity.require,
                  Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
              · by_cases h14 : nodeIndex == 14
                · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, h11, h12, h13, h14, level1_parent_equals_sum_of_children_spec,
                    SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
                    SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
                    SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
                    SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
                    SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
                    getStorage, setStorage, setMappingUint, Verity.require,
                    Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
                · exfalso; exact leaf_index_exhausted nodeIndex hLow hHigh h7 h8 h9 h10 h11 h12 h13 h14

/-! ### Root equals sum of leaves -/

/--
After `setLeaf`, the root equals the sum of all eight leaf weights.
-/
theorem root_equals_sum_of_leaves
    (nodeIndex stakePathID weight : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 7)
    (hHigh : nodeIndex <= 14) :
    let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
    root_equals_sum_of_leaves_spec s' := by
  let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
  have hL2 : level2_parent_equals_sum_of_children_spec s' := by
    simpa [s'] using level2_parent_equals_sum_of_children nodeIndex stakePathID weight s hLow hHigh
  have hL1 : level1_parent_equals_sum_of_children_spec s' := by
    simpa [s'] using level1_parent_equals_sum_of_children nodeIndex stakePathID weight s hLow hHigh
  have hRootLR : s'.storage 0 = add (s'.storage 1) (s'.storage 2) := by
    by_cases h7 : nodeIndex == 7
    · simp [s', SortitionTrees.setLeaf, SortitionTrees.rootSum, SortitionTrees.node1,
        SortitionTrees.node2, hLow, hHigh, h7, getStorage, setStorage, setMappingUint,
        Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
    · by_cases h8 : nodeIndex == 8
      · simp [s', SortitionTrees.setLeaf, SortitionTrees.rootSum, SortitionTrees.node1,
          SortitionTrees.node2, hLow, hHigh, h7, h8, getStorage, setStorage, setMappingUint,
          Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
      · by_cases h9 : nodeIndex == 9
        · simp [s', SortitionTrees.setLeaf, SortitionTrees.rootSum, SortitionTrees.node1,
            SortitionTrees.node2, hLow, hHigh, h7, h8, h9, getStorage, setStorage, setMappingUint,
            Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
        · by_cases h10 : nodeIndex == 10
          · simp [s', SortitionTrees.setLeaf, SortitionTrees.rootSum, SortitionTrees.node1,
              SortitionTrees.node2, hLow, hHigh, h7, h8, h9, h10, getStorage, setStorage, setMappingUint,
              Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
          · by_cases h11 : nodeIndex == 11
            · simp [s', SortitionTrees.setLeaf, SortitionTrees.rootSum, SortitionTrees.node1,
                SortitionTrees.node2, hLow, hHigh, h7, h8, h9, h10, h11, getStorage, setStorage, setMappingUint,
                Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
            · by_cases h12 : nodeIndex == 12
              · simp [s', SortitionTrees.setLeaf, SortitionTrees.rootSum, SortitionTrees.node1,
                  SortitionTrees.node2, hLow, hHigh, h7, h8, h9, h10, h11, h12, getStorage, setStorage, setMappingUint,
                  Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
              · by_cases h13 : nodeIndex == 13
                · simp [s', SortitionTrees.setLeaf, SortitionTrees.rootSum, SortitionTrees.node1,
                    SortitionTrees.node2, hLow, hHigh, h7, h8, h9, h10, h11, h12, h13, getStorage, setStorage, setMappingUint,
                    Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
                · by_cases h14 : nodeIndex == 14
                  · simp [s', SortitionTrees.setLeaf, SortitionTrees.rootSum, SortitionTrees.node1,
                      SortitionTrees.node2, hLow, hHigh, h7, h8, h9, h10, h11, h12, h13, h14, getStorage, setStorage, setMappingUint,
                      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
                  · exfalso; exact leaf_index_exhausted nodeIndex hLow hHigh h7 h8 h9 h10 h11 h12 h13 h14
  rcases hL2 with ⟨hN3, hN4, hN5, hN6⟩
  rcases hL1 with ⟨hN1, hN2⟩
  unfold root_equals_sum_of_leaves_spec leaf_sum
  calc
    s'.storage 0 = add (s'.storage 1) (s'.storage 2) := hRootLR
    _ = add (add (s'.storage 3) (s'.storage 4)) (add (s'.storage 5) (s'.storage 6)) := by
          rw [hN1, hN2]
    _ = add (add (add (s'.storage 7) (s'.storage 8)) (add (s'.storage 9) (s'.storage 10)))
            (add (add (s'.storage 11) (s'.storage 12)) (add (s'.storage 13) (s'.storage 14))) := by
          rw [hN3, hN4, hN5, hN6]

/-! ### Draw selects valid leaf -/

/--
Any successful `draw` resolves to one of the eight leaf node indices.
-/
theorem draw_selects_valid_leaf
    (ticket : Uint256) (s : ContractState)
    (hRoot : s.storage 0 != 0)
    (hInRange : ticket < s.storage 0) :
    let s' := ((SortitionTrees.draw ticket).run s).snd
    draw_selects_valid_leaf_spec s' := by
  unfold draw_selects_valid_leaf_spec
  dsimp
  rw [draw_selected_node ticket s hRoot hInRange]
  by_cases hN1 : ticket < s.storage 1
  · by_cases hN3 : ticket < s.storage 3
    · by_cases hL0 : ticket < s.storage 7
      · simp [hN1, hN3, hL0]; decide
      · simp [hN1, hN3, hL0]; decide
    · by_cases hL2 : sub ticket (s.storage 3) < s.storage 9
      · simp [hN1, hN3, hL2]; decide
      · simp [hN1, hN3, hL2]; decide
  · by_cases hN5 : sub ticket (s.storage 1) < s.storage 5
    · by_cases hL4 : sub ticket (s.storage 1) < s.storage 11
      · simp [hN1, hN5, hL4]; decide
      · simp [hN1, hN5, hL4]; decide
    · by_cases hL6 : sub (sub ticket (s.storage 1)) (s.storage 5) < s.storage 13
      · simp [hN1, hN5, hL6]; decide
      · simp [hN1, hN5, hL6]; decide

/-! ### Draw interval matches weights -/

/--
Draw follows the encoded ticket intervals in the 3-level tree.
-/
theorem draw_interval_matches_weights
    (ticket : Uint256) (s : ContractState)
    (hRoot : s.storage 0 != 0)
    (hInRange : ticket < s.storage 0) :
    let s' := ((SortitionTrees.draw ticket).run s).snd
    draw_interval_matches_weights_spec ticket s s' := by
  unfold draw_interval_matches_weights_spec
  dsimp
  intro _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- leaf0: ticket < n1 ∧ ticket < n3 ∧ ticket < l0
  · intro ⟨hN1, hN3, hL0⟩
    rw [draw_selected_node ticket s hRoot hInRange]
    simp [hN1, hN3, hL0]
  -- leaf1: ticket < n1 ∧ ticket < n3 ∧ l0 ≤ ticket
  · intro ⟨hN1, hN3, hL0ge⟩
    rw [draw_selected_node ticket s hRoot hInRange]
    have hNotL0 : ¬ ticket < s.storage 7 := Nat.not_lt_of_ge hL0ge
    simp [hN1, hN3, hNotL0]
  -- leaf2: ticket < n1 ∧ n3 ≤ ticket ∧ sub ticket n3 < l2
  · intro ⟨hN1, hN3ge, hL2⟩
    rw [draw_selected_node ticket s hRoot hInRange]
    have hNotN3 : ¬ ticket < s.storage 3 := Nat.not_lt_of_ge hN3ge
    simp [hN1, hNotN3, hL2]
  -- leaf3: ticket < n1 ∧ n3 ≤ ticket ∧ l2 ≤ sub ticket n3
  · intro ⟨hN1, hN3ge, hL2ge⟩
    rw [draw_selected_node ticket s hRoot hInRange]
    have hNotN3 : ¬ ticket < s.storage 3 := Nat.not_lt_of_ge hN3ge
    have hNotL2 : ¬ sub ticket (s.storage 3) < s.storage 9 := Nat.not_lt_of_ge hL2ge
    simp [hN1, hNotN3, hNotL2]
  -- leaf4: n1 ≤ ticket ∧ sub ticket n1 < n5 ∧ sub ticket n1 < l4
  · intro ⟨hN1ge, hN5, hL4⟩
    rw [draw_selected_node ticket s hRoot hInRange]
    have hNotN1 : ¬ ticket < s.storage 1 := Nat.not_lt_of_ge hN1ge
    simp [hNotN1, hN5, hL4]
  -- leaf5: n1 ≤ ticket ∧ sub ticket n1 < n5 ∧ l4 ≤ sub ticket n1
  · intro ⟨hN1ge, hN5, hL4ge⟩
    rw [draw_selected_node ticket s hRoot hInRange]
    have hNotN1 : ¬ ticket < s.storage 1 := Nat.not_lt_of_ge hN1ge
    have hNotL4 : ¬ sub ticket (s.storage 1) < s.storage 11 := Nat.not_lt_of_ge hL4ge
    simp [hNotN1, hN5, hNotL4]
  -- leaf6: n1 ≤ ticket ∧ n5 ≤ sub ticket n1 ∧ sub (sub ticket n1) n5 < l6
  · intro ⟨hN1ge, hN5ge, hL6⟩
    rw [draw_selected_node ticket s hRoot hInRange]
    have hNotN1 : ¬ ticket < s.storage 1 := Nat.not_lt_of_ge hN1ge
    have hNotN5 : ¬ sub ticket (s.storage 1) < s.storage 5 := Nat.not_lt_of_ge hN5ge
    simp [hNotN1, hNotN5, hL6]
  -- leaf7: n1 ≤ ticket ∧ n5 ≤ sub ticket n1 ∧ l6 ≤ sub (sub ticket n1) n5
  · intro ⟨hN1ge, hN5ge, hL6ge⟩
    rw [draw_selected_node ticket s hRoot hInRange]
    have hNotN1 : ¬ ticket < s.storage 1 := Nat.not_lt_of_ge hN1ge
    have hNotN5 : ¬ sub ticket (s.storage 1) < s.storage 5 := Nat.not_lt_of_ge hN5ge
    have hNotL6 : ¬ sub (sub ticket (s.storage 1)) (s.storage 5) < s.storage 13 := Nat.not_lt_of_ge hL6ge
    simp [hNotN1, hNotN5, hNotL6]

/-! ### Node ID bijection -/

/--
`setLeaf` writes matching forward and reverse mapping entries.
-/
theorem node_id_bijection
    (nodeIndex stakePathID weight : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 7)
    (hHigh : nodeIndex <= 14) :
    let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
    node_id_bijection_spec nodeIndex stakePathID s' := by
  have h15eq : 15 = SortitionTrees.nodeIndexesToIDs.slot := by decide
  have h16eq : 16 = SortitionTrees.IDsToNodeIndexes.slot := by decide
  by_cases h7 : nodeIndex == 7
  · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h15eq, h16eq, node_id_bijection_spec, getStorage,
      setStorage, setMappingUint, Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
  · by_cases h8 : nodeIndex == 8
    · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h15eq, h16eq, node_id_bijection_spec,
        getStorage, setStorage, setMappingUint, Verity.require, Verity.bind, Bind.bind, Contract.run,
        ContractResult.snd]
    · by_cases h9 : nodeIndex == 9
      · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h15eq, h16eq, node_id_bijection_spec,
          getStorage, setStorage, setMappingUint, Verity.require, Verity.bind, Bind.bind, Contract.run,
          ContractResult.snd]
      · by_cases h10 : nodeIndex == 10
        · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, h15eq, h16eq, node_id_bijection_spec,
            getStorage, setStorage, setMappingUint, Verity.require, Verity.bind, Bind.bind, Contract.run,
            ContractResult.snd]
        · by_cases h11 : nodeIndex == 11
          · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, h11, h15eq, h16eq, node_id_bijection_spec,
              getStorage, setStorage, setMappingUint, Verity.require, Verity.bind, Bind.bind, Contract.run,
              ContractResult.snd]
          · by_cases h12 : nodeIndex == 12
            · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, h11, h12, h15eq, h16eq, node_id_bijection_spec,
                getStorage, setStorage, setMappingUint, Verity.require, Verity.bind, Bind.bind, Contract.run,
                ContractResult.snd]
            · by_cases h13 : nodeIndex == 13
              · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, h11, h12, h13, h15eq, h16eq, node_id_bijection_spec,
                  getStorage, setStorage, setMappingUint, Verity.require, Verity.bind, Bind.bind, Contract.run,
                  ContractResult.snd]
              · by_cases h14 : nodeIndex == 14
                · simp [SortitionTrees.setLeaf, hLow, hHigh, h7, h8, h9, h10, h11, h12, h13, h14, h15eq, h16eq, node_id_bijection_spec,
                    getStorage, setStorage, setMappingUint, Verity.require, Verity.bind, Bind.bind, Contract.run,
                    ContractResult.snd]
                · exfalso; exact leaf_index_exhausted nodeIndex hLow hHigh h7 h8 h9 h10 h11 h12 h13 h14

/-! ### Root minus left equals right subtree -/

/--
After `setLeaf`, root - left subtree = right subtree.
-/
theorem root_minus_left_equals_right_subtree
    (nodeIndex stakePathID weight : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 7)
    (hHigh : nodeIndex <= 14) :
    let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
    root_minus_left_equals_right_subtree_spec s' := by
  let s' := ((SortitionTrees.setLeaf nodeIndex stakePathID weight).run s).snd
  have hL1 : level1_parent_equals_sum_of_children_spec s' := by
    simpa [s'] using level1_parent_equals_sum_of_children nodeIndex stakePathID weight s hLow hHigh
  have hRoot : root_equals_sum_of_leaves_spec s' := by
    simpa [s'] using root_equals_sum_of_leaves nodeIndex stakePathID weight s hLow hHigh
  have hL2 : level2_parent_equals_sum_of_children_spec s' := by
    simpa [s'] using level2_parent_equals_sum_of_children nodeIndex stakePathID weight s hLow hHigh
  rcases hL1 with ⟨hN1, hN2⟩
  rcases hL2 with ⟨hN3, hN4, hN5, hN6⟩
  have hRootLR : s'.storage 0 = add (s'.storage 1) (s'.storage 2) := by
    unfold root_equals_sum_of_leaves_spec at hRoot
    unfold leaf_sum at hRoot
    calc
      s'.storage 0
        = add (add (add (s'.storage 7) (s'.storage 8)) (add (s'.storage 9) (s'.storage 10)))
              (add (add (s'.storage 11) (s'.storage 12)) (add (s'.storage 13) (s'.storage 14))) := hRoot
      _ = add (add (s'.storage 3) (s'.storage 4)) (add (s'.storage 5) (s'.storage 6)) := by
            rw [← hN3, ← hN4, ← hN5, ← hN6]
      _ = add (s'.storage 1) (s'.storage 2) := by rw [← hN1, ← hN2]
  unfold root_minus_left_equals_right_subtree_spec
  dsimp
  apply Verity.Core.Uint256.add_right_cancel
  calc
    ((s'.storage 0 - s'.storage 1) + s'.storage 1) = s'.storage 0 := by
      exact Verity.Core.Uint256.sub_add_cancel_left (s'.storage 0) (s'.storage 1)
    _ = add (s'.storage 1) (s'.storage 2) := hRootLR
    _ = (s'.storage 2) + (s'.storage 1) := by
          exact Verity.Core.Uint256.add_comm (s'.storage 1) (s'.storage 2)

/-! ### Sequential setLeaf preserves root conservation -/

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
  unfold sequential_setLeaf_root_conservation_spec
  exact root_equals_sum_of_leaves idx2 id2 w2
    ((SortitionTrees.setLeaf idx1 id1 w1).run s).snd hLow2 hHigh2

/-! ### Overflow safety under explicit no-wrap assumptions -/

/--
If the root really is the sum of its two children without modular wraparound,
then it is at least as large as each child.
-/
theorem overflow_safety_of_no_wrap
    (s' : ContractState)
    (hRoot : s'.storage 0 = add (s'.storage 1) (s'.storage 2))
    (hNoWrap : (s'.storage 1 : Nat) + (s'.storage 2 : Nat) ≤ Verity.Core.MAX_UINT256) :
    overflow_safety_spec s' := by
  unfold overflow_safety_spec
  exact ⟨ge_left_of_eq_add_no_wrap hRoot hNoWrap, ge_right_of_eq_add_no_wrap hRoot hNoWrap⟩

/--
If each level-1 node really is the sum of its two children without modular
wraparound, then each parent is at least as large as each child.
-/
theorem level1_overflow_safety_of_no_wrap
    (s' : ContractState)
    (hNode1 : s'.storage 1 = add (s'.storage 3) (s'.storage 4))
    (hNode2 : s'.storage 2 = add (s'.storage 5) (s'.storage 6))
    (hNode1NoWrap : (s'.storage 3 : Nat) + (s'.storage 4 : Nat) ≤ Verity.Core.MAX_UINT256)
    (hNode2NoWrap : (s'.storage 5 : Nat) + (s'.storage 6 : Nat) ≤ Verity.Core.MAX_UINT256) :
    level1_overflow_safety_spec s' := by
  unfold level1_overflow_safety_spec
  exact ⟨ge_left_of_eq_add_no_wrap hNode1 hNode1NoWrap,
    ge_right_of_eq_add_no_wrap hNode1 hNode1NoWrap,
    ge_left_of_eq_add_no_wrap hNode2 hNode2NoWrap,
    ge_right_of_eq_add_no_wrap hNode2 hNode2NoWrap⟩

/-! ### removeLeaf correctness -/

private theorem removeLeaf_leaf7_summary (s : ContractState) :
    let s' := ((SortitionTrees.removeLeaf 7).run s).snd
    s'.storage 7 = 0 ∧
      s'.storageMapUint 15 7 = 0 ∧
      s'.storageMapUint 16 (s.storageMapUint 15 7) = 0 := by
  have hLow : (7 : Uint256) >= 7 := by decide
  have hHigh : (7 : Uint256) <= 14 := by decide
  simp [SortitionTrees.removeLeaf,
    hLow, hHigh,
    SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
    SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
    SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
    SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
    SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
    getStorage, getMappingUint, setStorage, setMappingUint, Verity.require,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem removeLeaf_leaf8_summary (s : ContractState) :
    let s' := ((SortitionTrees.removeLeaf 8).run s).snd
    s'.storage 8 = 0 ∧
      s'.storageMapUint 15 8 = 0 ∧
      s'.storageMapUint 16 (s.storageMapUint 15 8) = 0 := by
  have hLow : (8 : Uint256) >= 7 := by decide
  have hHigh : (8 : Uint256) <= 14 := by decide
  simp [SortitionTrees.removeLeaf,
    hLow, hHigh,
    SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
    SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
    SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
    SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
    SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
    getStorage, getMappingUint, setStorage, setMappingUint, Verity.require,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem removeLeaf_leaf9_summary (s : ContractState) :
    let s' := ((SortitionTrees.removeLeaf 9).run s).snd
    s'.storage 9 = 0 ∧
      s'.storageMapUint 15 9 = 0 ∧
      s'.storageMapUint 16 (s.storageMapUint 15 9) = 0 := by
  have hLow : (9 : Uint256) >= 7 := by decide
  have hHigh : (9 : Uint256) <= 14 := by decide
  simp [SortitionTrees.removeLeaf,
    hLow, hHigh,
    SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
    SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
    SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
    SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
    SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
    getStorage, getMappingUint, setStorage, setMappingUint, Verity.require,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem removeLeaf_leaf10_summary (s : ContractState) :
    let s' := ((SortitionTrees.removeLeaf 10).run s).snd
    s'.storage 10 = 0 ∧
      s'.storageMapUint 15 10 = 0 ∧
      s'.storageMapUint 16 (s.storageMapUint 15 10) = 0 := by
  have hLow : (10 : Uint256) >= 7 := by decide
  have hHigh : (10 : Uint256) <= 14 := by decide
  simp [SortitionTrees.removeLeaf,
    hLow, hHigh,
    SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
    SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
    SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
    SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
    SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
    getStorage, getMappingUint, setStorage, setMappingUint, Verity.require,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem removeLeaf_leaf11_summary (s : ContractState) :
    let s' := ((SortitionTrees.removeLeaf 11).run s).snd
    s'.storage 11 = 0 ∧
      s'.storageMapUint 15 11 = 0 ∧
      s'.storageMapUint 16 (s.storageMapUint 15 11) = 0 := by
  have hLow : (11 : Uint256) >= 7 := by decide
  have hHigh : (11 : Uint256) <= 14 := by decide
  simp [SortitionTrees.removeLeaf,
    hLow, hHigh,
    SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
    SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
    SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
    SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
    SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
    getStorage, getMappingUint, setStorage, setMappingUint, Verity.require,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem removeLeaf_leaf12_summary (s : ContractState) :
    let s' := ((SortitionTrees.removeLeaf 12).run s).snd
    s'.storage 12 = 0 ∧
      s'.storageMapUint 15 12 = 0 ∧
      s'.storageMapUint 16 (s.storageMapUint 15 12) = 0 := by
  have hLow : (12 : Uint256) >= 7 := by decide
  have hHigh : (12 : Uint256) <= 14 := by decide
  simp [SortitionTrees.removeLeaf,
    hLow, hHigh,
    SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
    SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
    SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
    SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
    SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
    getStorage, getMappingUint, setStorage, setMappingUint, Verity.require,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem removeLeaf_leaf13_summary (s : ContractState) :
    let s' := ((SortitionTrees.removeLeaf 13).run s).snd
    s'.storage 13 = 0 ∧
      s'.storageMapUint 15 13 = 0 ∧
      s'.storageMapUint 16 (s.storageMapUint 15 13) = 0 := by
  have hLow : (13 : Uint256) >= 7 := by decide
  have hHigh : (13 : Uint256) <= 14 := by decide
  simp [SortitionTrees.removeLeaf,
    hLow, hHigh,
    SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
    SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
    SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
    SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
    SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
    getStorage, getMappingUint, setStorage, setMappingUint, Verity.require,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem removeLeaf_leaf14_summary (s : ContractState) :
    let s' := ((SortitionTrees.removeLeaf 14).run s).snd
    s'.storage 14 = 0 ∧
      s'.storageMapUint 15 14 = 0 ∧
      s'.storageMapUint 16 (s.storageMapUint 15 14) = 0 := by
  have hLow : (14 : Uint256) >= 7 := by decide
  have hHigh : (14 : Uint256) <= 14 := by decide
  simp [SortitionTrees.removeLeaf,
    hLow, hHigh,
    SortitionTrees.rootSum, SortitionTrees.node1, SortitionTrees.node2,
    SortitionTrees.node3, SortitionTrees.node4, SortitionTrees.node5, SortitionTrees.node6,
    SortitionTrees.leaf0, SortitionTrees.leaf1, SortitionTrees.leaf2, SortitionTrees.leaf3,
    SortitionTrees.leaf4, SortitionTrees.leaf5, SortitionTrees.leaf6, SortitionTrees.leaf7,
    SortitionTrees.nodeIndexesToIDs, SortitionTrees.IDsToNodeIndexes,
    getStorage, getMappingUint, setStorage, setMappingUint, Verity.require,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem removeLeaf_selected_slot_zero
    (nodeIndex : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 7)
    (hHigh : nodeIndex <= 14) :
    let s' := ((SortitionTrees.removeLeaf nodeIndex).run s).snd
    s'.storage nodeIndex.val = 0 := by
  by_cases h7 : nodeIndex == 7
  · have hEq7 : nodeIndex = 7 := by simpa using h7
    subst hEq7
    exact (removeLeaf_leaf7_summary s).1
  · by_cases h8 : nodeIndex == 8
    · have hEq8 : nodeIndex = 8 := by simpa using h8
      subst hEq8
      exact (removeLeaf_leaf8_summary s).1
    · by_cases h9 : nodeIndex == 9
      · have hEq9 : nodeIndex = 9 := by simpa using h9
        subst hEq9
        exact (removeLeaf_leaf9_summary s).1
      · by_cases h10 : nodeIndex == 10
        · have hEq10 : nodeIndex = 10 := by simpa using h10
          subst hEq10
          exact (removeLeaf_leaf10_summary s).1
        · by_cases h11 : nodeIndex == 11
          · have hEq11 : nodeIndex = 11 := by simpa using h11
            subst hEq11
            exact (removeLeaf_leaf11_summary s).1
          · by_cases h12 : nodeIndex == 12
            · have hEq12 : nodeIndex = 12 := by simpa using h12
              subst hEq12
              exact (removeLeaf_leaf12_summary s).1
            · by_cases h13 : nodeIndex == 13
              · have hEq13 : nodeIndex = 13 := by simpa using h13
                subst hEq13
                exact (removeLeaf_leaf13_summary s).1
              · by_cases h14 : nodeIndex == 14
                · have hEq14 : nodeIndex = 14 := by simpa using h14
                  subst hEq14
                  exact (removeLeaf_leaf14_summary s).1
                · exfalso; exact leaf_index_exhausted nodeIndex hLow hHigh h7 h8 h9 h10 h11 h12 h13 h14

private theorem removeLeaf_clears_associated_maps
    (nodeIndex stakePathID : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 7)
    (hHigh : nodeIndex <= 14)
    (hStakePathID : s.storageMapUint 15 nodeIndex = stakePathID) :
    let s' := ((SortitionTrees.removeLeaf nodeIndex).run s).snd
    s'.storageMapUint 15 nodeIndex = 0 ∧ s'.storageMapUint 16 stakePathID = 0 := by
  by_cases h7 : nodeIndex == 7
  · have hEq7 : nodeIndex = 7 := by simpa using h7
    subst hEq7
    exact ⟨(removeLeaf_leaf7_summary s).2.1, by simpa [hStakePathID] using (removeLeaf_leaf7_summary s).2.2⟩
  · by_cases h8 : nodeIndex == 8
    · have hEq8 : nodeIndex = 8 := by simpa using h8
      subst hEq8
      exact ⟨(removeLeaf_leaf8_summary s).2.1, by simpa [hStakePathID] using (removeLeaf_leaf8_summary s).2.2⟩
    · by_cases h9 : nodeIndex == 9
      · have hEq9 : nodeIndex = 9 := by simpa using h9
        subst hEq9
        exact ⟨(removeLeaf_leaf9_summary s).2.1, by simpa [hStakePathID] using (removeLeaf_leaf9_summary s).2.2⟩
      · by_cases h10 : nodeIndex == 10
        · have hEq10 : nodeIndex = 10 := by simpa using h10
          subst hEq10
          exact ⟨(removeLeaf_leaf10_summary s).2.1, by simpa [hStakePathID] using (removeLeaf_leaf10_summary s).2.2⟩
        · by_cases h11 : nodeIndex == 11
          · have hEq11 : nodeIndex = 11 := by simpa using h11
            subst hEq11
            exact ⟨(removeLeaf_leaf11_summary s).2.1, by simpa [hStakePathID] using (removeLeaf_leaf11_summary s).2.2⟩
          · by_cases h12 : nodeIndex == 12
            · have hEq12 : nodeIndex = 12 := by simpa using h12
              subst hEq12
              exact ⟨(removeLeaf_leaf12_summary s).2.1, by simpa [hStakePathID] using (removeLeaf_leaf12_summary s).2.2⟩
            · by_cases h13 : nodeIndex == 13
              · have hEq13 : nodeIndex = 13 := by simpa using h13
                subst hEq13
                exact ⟨(removeLeaf_leaf13_summary s).2.1, by simpa [hStakePathID] using (removeLeaf_leaf13_summary s).2.2⟩
              · by_cases h14 : nodeIndex == 14
                · have hEq14 : nodeIndex = 14 := by simpa using h14
                  subst hEq14
                  exact ⟨(removeLeaf_leaf14_summary s).2.1, by simpa [hStakePathID] using (removeLeaf_leaf14_summary s).2.2⟩
                · exfalso; exact leaf_index_exhausted nodeIndex hLow hHigh h7 h8 h9 h10 h11 h12 h13 h14

/--
After `removeLeaf`, the targeted leaf is zeroed.
-/
theorem remove_leaf_zeroed
    (nodeIndex : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 7)
    (hHigh : nodeIndex <= 14) :
    let s' := ((SortitionTrees.removeLeaf nodeIndex).run s).snd
    remove_leaf_zeroed_spec nodeIndex s' := by
  unfold remove_leaf_zeroed_spec
  exact removeLeaf_selected_slot_zero nodeIndex s hLow hHigh

/--
After `removeLeaf`, the forward and reverse mappings for the removed juror are cleared,
provided `stakePathID` is the ID currently associated with `nodeIndex`.
-/
theorem remove_leaf_clears_associated_id
    (nodeIndex stakePathID : Uint256) (s : ContractState)
    (hLow : nodeIndex >= 7)
    (hHigh : nodeIndex <= 14)
    (hStakePathID : s.storageMapUint 15 nodeIndex = stakePathID) :
    let s' := ((SortitionTrees.removeLeaf nodeIndex).run s).snd
    remove_leaf_clears_id_spec nodeIndex stakePathID s' := by
  unfold remove_leaf_clears_id_spec
  exact removeLeaf_clears_associated_maps nodeIndex stakePathID s hLow hHigh hStakePathID

end Benchmark.Cases.Kleros.SortitionTrees
