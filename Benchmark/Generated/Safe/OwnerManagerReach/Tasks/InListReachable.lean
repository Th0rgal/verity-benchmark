import Benchmark.Cases.Safe.OwnerManagerReach.Specs

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
Certora `inListReachable` invariant preservation under `addOwner`.

Given that in the pre-state every node with a non-zero successor is reachable
from SENTINEL, show that the same holds in the post-state after inserting
`owner` at the head of the linked list.

Proof strategy: SENTINEL is trivially reachable (reflexivity). The new owner
is reachable via [SENTINEL, owner]. For any other key with a non-zero successor,
its next pointer is unchanged, so we can lift its pre-state witness chain to
the post-state and prepend the new path SENTINEL → owner → old_head.
-/
theorem in_list_reachable
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    -- Pre-state invariant
    (_hPreSentNZ : next s SENTINEL ≠ zeroAddress)
    (hPreReach : ∀ key : Address, next s key ≠ zeroAddress → reachable s SENTINEL key)
    -- Acyclicity: SENTINEL does not appear in any chain from SENTINEL's successor.
    (hAcyclic : ∀ key : Address, ∀ chain : List Address,
      chain.head? = some (next s SENTINEL) →
      chain.getLast? = some key →
      isChain s chain →
      SENTINEL ∉ chain)
    -- owner is fresh (not in the list)
    (hOwnerFresh : ∀ key : Address, ∀ chain : List Address,
      chain.head? = some (next s SENTINEL) →
      chain.getLast? = some key →
      isChain s chain →
      owner ∉ chain) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    in_list_reachable_spec s s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Safe.OwnerManagerReach
