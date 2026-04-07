import Verity.Specs.Common
import Benchmark.Cases.Safe.OwnerManagerReach.Contract

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/-
  Specifications for the Safe OwnerManager linked list reachability properties.
  These correspond to invariants from the Certora OwnerReach.spec.

  The key idea: reachability is witnessed by a concrete list of addresses
  that forms a valid chain in the `owners` mapping, turning the transitive
  closure into induction on list indices.

  Storage layout (from verity_contract OwnerManager):
    slot 0 (mapping): owners — linked list next pointers (Address → Address)
    slot 1: ownerCount
-/

-- Linked list next-pointer accessor (reads storageMap slot 0 as Address).
def next (s : ContractState) (a : Address) : Address :=
  wordToAddress (s.storageMap 0 a)

-- A list of addresses forms a valid chain in the owners mapping:
-- each element's `next` is the following element.
def isChain (s : ContractState) : List Address → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => next s a = b ∧ isChain s (b :: rest)

-- Reachability via a witness chain: `a` reaches `b` if there is a
-- chain starting at `a` and ending at `b`.
def reachable (s : ContractState) (a b : Address) : Prop :=
  ∃ chain : List Address,
    chain.head? = some a ∧
    chain.getLast? = some b ∧
    isChain s chain

/--
  Certora `inListReachable` invariant:
    ghostOwners[SENTINEL] != 0 &&
    (forall address key. ghostOwners[key] != 0 => reach(SENTINEL, key))

  After executing `addOwner`, every node with a non-zero successor in the
  post-state is reachable from SENTINEL via the owners mapping.
-/
def in_list_reachable_spec
    (_s s' : ContractState) : Prop :=
  next s' SENTINEL ≠ zeroAddress ∧
  ∀ key : Address, next s' key ≠ zeroAddress → reachable s' SENTINEL key

end Benchmark.Cases.Safe.OwnerManagerReach
