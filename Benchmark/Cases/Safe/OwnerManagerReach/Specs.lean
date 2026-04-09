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

/-! ## Core definitions -/

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

/-! ## Invariant: well-formed owner list

  The `ownerListInvariant` combines the Certora `inListReachable` and
  `reachableInList` invariants into a single biconditional property.
  Together they state that the set of nodes with non-zero successors
  is exactly the set of nodes reachable from SENTINEL.

  Certora originals:
    inListReachable:
      ghostOwners[SENTINEL] != 0 ∧
      (∀ key. ghostOwners[key] != 0 → reach(SENTINEL, key))
    reachableInList:
      (∀ X Y. reach(X, Y) → X = Y ∨ Y = 0 ∨ ghostOwners[Y] != 0)
-/

/--
  Certora `inListReachable` invariant:
  The list is non-empty (SENTINEL has a successor) and every node with a
  non-zero successor is reachable from SENTINEL.
-/
def inListReachable (s : ContractState) : Prop :=
  next s SENTINEL ≠ zeroAddress ∧
  ∀ key : Address, next s key ≠ zeroAddress → reachable s SENTINEL key

/--
  Certora `reachableInList` invariant:
  Every address reachable from any node is either the source itself,
  the zero address, or has a non-zero successor (i.e. is in the list).

  Intuitively: reachability doesn't "leak" to addresses outside the list.
-/
def reachableInList (s : ContractState) : Prop :=
  ∀ x y : Address, reachable s x y → x = y ∨ y = zeroAddress ∨ next s y ≠ zeroAddress

/--
  Combined owner list invariant: the list is non-empty, and membership
  (having a non-zero successor) is equivalent to reachability from SENTINEL.
  This merges inListReachable and reachableInList into a single property.

  The `key ≠ zeroAddress` guard matches Solidity semantics: address(0) is
  never a valid owner (`require(owner != address(0))`), and in the Safe
  contract `owners[address(0)]` is always 0. This guard excludes the zero
  address from the biconditional since it is outside the owner domain.
-/
def ownerListInvariant (s : ContractState) : Prop :=
  next s SENTINEL ≠ zeroAddress ∧
  (∀ key : Address, key ≠ zeroAddress →
    (next s key ≠ zeroAddress ↔ reachable s SENTINEL key))

/-! ## Acyclicity and termination

  These definitions support proving that the linked list is acyclic
  (SENTINEL appears only at the boundaries, no internal loops) and
  that every path terminates. Proving these as theorems rather than
  assuming them would eliminate the hAcyclic and hOwnerFresh axioms
  from the current proofs.
-/

-- A chain has no duplicate addresses.
def noDuplicates : List Address → Prop
  | [] => True
  | a :: rest => a ∉ rest ∧ noDuplicates rest

/--
  Acyclicity: the linked list from SENTINEL has no internal cycles.
  For any duplicate-free chain starting at SENTINEL's successor and
  ending at a non-SENTINEL key, SENTINEL does not appear in the chain.

  The `noDuplicates` condition is essential: in a circular list
  (e.g. SENTINEL → o1 → o2 → o3 → SENTINEL), the chain
  [o1, o2, o3, SENTINEL, o1] is a valid `isChain` that contains
  SENTINEL and ends at o1 ≠ SENTINEL. But it has a duplicate (o1),
  so `noDuplicates` excludes it. Without duplicates, chains ending
  at key ≠ SENTINEL are strict prefixes that never reach SENTINEL.
-/
def acyclic (s : ContractState) : Prop :=
  ∀ key : Address, key ≠ SENTINEL → ∀ chain : List Address,
    chain.head? = some (next s SENTINEL) →
    chain.getLast? = some key →
    isChain s chain →
    noDuplicates chain →
    SENTINEL ∉ chain

/--
  Freshness of a given address: it does not appear in any duplicate-free
  chain starting from SENTINEL's successor. This is a consequence of
  acyclicity + the address having a zero mapping value.
-/
def freshInList (s : ContractState) (addr : Address) : Prop :=
  ∀ key : Address, ∀ chain : List Address,
    chain.head? = some (next s SENTINEL) →
    chain.getLast? = some key →
    isChain s chain →
    noDuplicates chain →
    addr ∉ chain

/-! ## Per-function preservation specs

  Each theorem states: given the invariant holds on the pre-state,
  it holds on the post-state after the function executes.
  The legacy `in_list_reachable_spec` is kept for backward compatibility
  with the existing addOwner proof.
-/

-- Legacy spec for backward compatibility with the existing proof.
def in_list_reachable_spec
    (_s s' : ContractState) : Prop :=
  next s' SENTINEL ≠ zeroAddress ∧
  ∀ key : Address, next s' key ≠ zeroAddress → reachable s' SENTINEL key

-- Preservation of ownerListInvariant under addOwner.
def addOwner_preserves_invariant
    (s s' : ContractState) : Prop :=
  ownerListInvariant s → ownerListInvariant s'

-- Preservation of ownerListInvariant under removeOwner.
def removeOwner_preserves_invariant
    (s s' : ContractState) : Prop :=
  ownerListInvariant s → ownerListInvariant s'

-- Preservation of ownerListInvariant under swapOwner.
def swapOwner_preserves_invariant
    (s s' : ContractState) : Prop :=
  ownerListInvariant s → ownerListInvariant s'

-- Establishment of ownerListInvariant by setupOwners.
-- Unlike the other specs, this does not require a pre-state invariant:
-- it is the base case.
def setupOwners_establishes_invariant
    (s' : ContractState) : Prop :=
  ownerListInvariant s'

end Benchmark.Cases.Safe.OwnerManagerReach
