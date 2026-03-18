import Benchmark.Cases.Kleros.SortitionTrees.Specs

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity
open Verity.EVM.Uint256

/--
Each parent node stores the sum of its direct children in the benchmark slice.
-/
theorem parent_equals_sum_of_children
    (s' : ContractState) :
    parent_equals_sum_of_children_spec s' ->
    s'.storage 1 = add (s'.storage 3) (s'.storage 4) /\
    s'.storage 2 = add (s'.storage 5) (s'.storage 6) := by
  intro hParent
  simpa [parent_equals_sum_of_children_spec] using hParent

/--
The root stores the sum of the four leaf weights.
-/
theorem root_equals_sum_of_leaves
    (s' : ContractState) :
    root_equals_sum_of_leaves_spec s' ->
    s'.storage 0 = leaf_sum s' := by
  intro hRoot
  simpa [root_equals_sum_of_leaves_spec] using hRoot

/--
The draw interval decomposition matches the four leaf weights.
-/
theorem draw_interval_matches_weights
    (ticket : Uint256) (s s' : ContractState) :
    draw_interval_matches_weights_spec ticket s s' ->
    ticket < s.storage 0 ->
    (
      (ticket < s.storage 3 -> s'.storage 9 = 3) /\
      (s.storage 3 <= ticket /\ ticket < s.storage 1 -> s'.storage 9 = 4) /\
      (s.storage 1 <= ticket /\ ticket < add (s.storage 1) (s.storage 5) -> s'.storage 9 = 5) /\
      (add (s.storage 1) (s.storage 5) <= ticket -> s'.storage 9 = 6)
    ) := by
  intro hDraw hInRange
  exact hDraw hInRange

/--
The explicit node-id tables are inverse on the four benchmark leaves.
-/
theorem node_id_bijection
    (s' : ContractState) :
    node_id_bijection_spec s' ->
    s'.storageMapUint 8 (s'.storageMapUint 7 3) = 3 /\
    s'.storageMapUint 8 (s'.storageMapUint 7 4) = 4 /\
    s'.storageMapUint 8 (s'.storageMapUint 7 5) = 5 /\
    s'.storageMapUint 8 (s'.storageMapUint 7 6) = 6 := by
  intro hBijection
  simpa [node_id_bijection_spec] using hBijection

/--
If the tree's parent sums are consistent and the root equals the sum of all
leaves, then removing the left subtree weight from the root leaves exactly the
right subtree weight.
-/
theorem root_minus_left_equals_right_subtree
    (s' : ContractState) :
    parent_equals_sum_of_children_spec s' ->
    root_equals_sum_of_leaves_spec s' ->
    s'.storage 0 - s'.storage 1 = s'.storage 2 := by
  intro hParent hRoot
  unfold parent_equals_sum_of_children_spec at hParent
  rcases hParent with ⟨hLeft, hRight⟩
  unfold root_equals_sum_of_leaves_spec at hRoot
  unfold leaf_sum at hRoot
  rw [hRoot, hLeft, hRight]
  rw [Verity.Core.Uint256.add_comm (add (s'.storage 3) (s'.storage 4)) (add (s'.storage 5) (s'.storage 6))]
  exact Verity.Core.Uint256.sub_add_cancel (add (s'.storage 5) (s'.storage 6)) (add (s'.storage 3) (s'.storage 4))

end Benchmark.Cases.Kleros.SortitionTrees
