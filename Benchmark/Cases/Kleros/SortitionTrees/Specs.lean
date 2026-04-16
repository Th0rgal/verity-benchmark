import Verity.Specs.Common
import Benchmark.Cases.Kleros.SortitionTrees.Contract

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity
open Verity.EVM.Uint256

/-! ### Helpers -/

/-- Sum of all eight leaf weights. -/
def leaf_sum (s : ContractState) : Uint256 :=
  add
    (add (add (s.storage 7) (s.storage 8)) (add (s.storage 9) (s.storage 10)))
    (add (add (s.storage 11) (s.storage 12)) (add (s.storage 13) (s.storage 14)))

/-! ### Original properties (adapted to 8-leaf tree) -/

/-- Each level-2 internal node equals the sum of its two leaf children. -/
def level2_parent_equals_sum_of_children_spec (s' : ContractState) : Prop :=
  s'.storage 3 = add (s'.storage 7)  (s'.storage 8)  ∧
  s'.storage 4 = add (s'.storage 9)  (s'.storage 10) ∧
  s'.storage 5 = add (s'.storage 11) (s'.storage 12) ∧
  s'.storage 6 = add (s'.storage 13) (s'.storage 14)

/-- Each level-1 internal node equals the sum of its two level-2 children. -/
def level1_parent_equals_sum_of_children_spec (s' : ContractState) : Prop :=
  s'.storage 1 = add (s'.storage 3) (s'.storage 4) ∧
  s'.storage 2 = add (s'.storage 5) (s'.storage 6)

/-- The root equals the total stake across all eight leaves. -/
def root_equals_sum_of_leaves_spec (s' : ContractState) : Prop :=
  s'.storage 0 = leaf_sum s'

/-- Root minus left subtree equals right subtree. -/
def root_minus_left_equals_right_subtree_spec (s' : ContractState) : Prop :=
  s'.storage 0 - s'.storage 1 = s'.storage 2

/-- Forward and reverse ID mappings are consistent for the given node. -/
def node_id_bijection_spec (nodeIndex stakePathID : Uint256) (s' : ContractState) : Prop :=
  s'.storageMapUint 15 nodeIndex = stakePathID ∧
  s'.storageMapUint 16 stakePathID = nodeIndex

/-! ### Draw properties (adapted to 8-leaf tree) -/

/-- Any successful draw resolves to a valid leaf index (7..14). -/
def draw_selects_valid_leaf_spec (s' : ContractState) : Prop :=
  7 <= s'.storage 17 ∧ s'.storage 17 <= 14

/-- Draw intervals match leaf weights (3-level traversal). -/
def draw_interval_matches_weights_spec (ticket : Uint256) (s : ContractState) (s' : ContractState) : Prop :=
  ticket < s.storage 0 →
  (
    -- Left subtree, node3, leaf0
    (ticket < s.storage 1 ∧ ticket < s.storage 3 ∧ ticket < s.storage 7
      → s'.storage 17 = 7) ∧
    -- Left subtree, node3, leaf1
    (ticket < s.storage 1 ∧ ticket < s.storage 3 ∧ s.storage 7 ≤ ticket
      → s'.storage 17 = 8) ∧
    -- Left subtree, node4, leaf2
    (ticket < s.storage 1 ∧ s.storage 3 ≤ ticket ∧ sub ticket (s.storage 3) < s.storage 9
      → s'.storage 17 = 9) ∧
    -- Left subtree, node4, leaf3
    (ticket < s.storage 1 ∧ s.storage 3 ≤ ticket ∧ s.storage 9 ≤ sub ticket (s.storage 3)
      → s'.storage 17 = 10) ∧
    -- Right subtree, node5, leaf4
    (s.storage 1 ≤ ticket ∧ sub ticket (s.storage 1) < s.storage 5 ∧ sub ticket (s.storage 1) < s.storage 11
      → s'.storage 17 = 11) ∧
    -- Right subtree, node5, leaf5
    (s.storage 1 ≤ ticket ∧ sub ticket (s.storage 1) < s.storage 5 ∧ s.storage 11 ≤ sub ticket (s.storage 1)
      → s'.storage 17 = 12) ∧
    -- Right subtree, node6, leaf6
    (s.storage 1 ≤ ticket ∧ s.storage 5 ≤ sub ticket (s.storage 1) ∧ sub (sub ticket (s.storage 1)) (s.storage 5) < s.storage 13
      → s'.storage 17 = 13) ∧
    -- Right subtree, node6, leaf7
    (s.storage 1 ≤ ticket ∧ s.storage 5 ≤ sub ticket (s.storage 1) ∧ s.storage 13 ≤ sub (sub ticket (s.storage 1)) (s.storage 5)
      → s'.storage 17 = 14)
  )

/-! ### New properties: overflow safety -/

/-- After setLeaf, the root is at least as large as each level-1 child (no wrapping). -/
def overflow_safety_spec (s' : ContractState) : Prop :=
  s'.storage 0 >= s'.storage 1 ∧
  s'.storage 0 >= s'.storage 2

/-- After setLeaf, each level-1 node is at least as large as each of its level-2 children. -/
def level1_overflow_safety_spec (s' : ContractState) : Prop :=
  s'.storage 1 >= s'.storage 3 ∧
  s'.storage 1 >= s'.storage 4 ∧
  s'.storage 2 >= s'.storage 5 ∧
  s'.storage 2 >= s'.storage 6

/-! ### New properties: removeLeaf -/

/-- After removeLeaf, the removed leaf has weight zero. -/
def remove_leaf_zeroed_spec (nodeIndex : Uint256) (s' : ContractState) : Prop :=
  s'.storage nodeIndex.val = 0

/-- After removeLeaf, the ID mappings for the removed node are cleared. -/
def remove_leaf_clears_id_spec (nodeIndex stakePathID : Uint256) (s' : ContractState) : Prop :=
  s'.storageMapUint 15 nodeIndex = 0 ∧
  s'.storageMapUint 16 stakePathID = 0

/-! ### New properties: multi-operation invariant -/

/-- After two consecutive setLeaf calls, the root still equals the sum of all leaves.
    This proves the invariant is inductive (not just base-case). -/
def sequential_setLeaf_root_conservation_spec (s'' : ContractState) : Prop :=
  s''.storage 0 = leaf_sum s''

end Benchmark.Cases.Kleros.SortitionTrees
