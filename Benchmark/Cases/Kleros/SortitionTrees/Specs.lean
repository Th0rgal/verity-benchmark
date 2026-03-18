import Verity.Specs.Common
import Benchmark.Cases.Kleros.SortitionTrees.Contract

namespace Benchmark.Cases.Kleros.SortitionTrees

open Verity
open Verity.EVM.Uint256

def leaf_sum (s : ContractState) : Uint256 :=
  add (add (s.storage 3) (s.storage 4)) (add (s.storage 5) (s.storage 6))

def parent_equals_sum_of_children_spec (s' : ContractState) : Prop :=
  s'.storage 1 = add (s'.storage 3) (s'.storage 4) /\
  s'.storage 2 = add (s'.storage 5) (s'.storage 6)

def root_equals_sum_of_leaves_spec (s' : ContractState) : Prop :=
  s'.storage 0 = leaf_sum s'

def draw_interval_matches_weights_spec (ticket : Uint256) (s s' : ContractState) : Prop :=
  ticket < s.storage 0 ->
  (
    (ticket < s.storage 3 -> s'.storage 9 = 3) /\
    (s.storage 3 <= ticket /\ ticket < s.storage 1 -> s'.storage 9 = 4) /\
    (s.storage 1 <= ticket /\ ticket < add (s.storage 1) (s.storage 5) -> s'.storage 9 = 5) /\
    (add (s.storage 1) (s.storage 5) <= ticket -> s'.storage 9 = 6)
  )

def node_id_bijection_spec (s' : ContractState) : Prop :=
  s'.storageMapUint 8 (s'.storageMapUint 7 3) = 3 /\
  s'.storageMapUint 8 (s'.storageMapUint 7 4) = 4 /\
  s'.storageMapUint 8 (s'.storageMapUint 7 5) = 5 /\
  s'.storageMapUint 8 (s'.storageMapUint 7 6) = 6

end Benchmark.Cases.Kleros.SortitionTrees
