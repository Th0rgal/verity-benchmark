import Benchmark.Cases.Safe.OwnerManagerReach.Specs

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
addOwner preserves acyclicity of the owner linked list.

After addOwner(owner), the list becomes:
  SENTINEL → owner → old_head → ... → SENTINEL

Proof strategy: owner was fresh (not in any existing chain). SENTINEL's
new successor is owner (not SENTINEL). The tail old_head → ... is
unchanged from the pre-state. By pre-state acyclicity, SENTINEL didn't
appear in the old tail. Since owner ≠ SENTINEL and owner was fresh,
SENTINEL still doesn't appear in any post-state chain starting from
SENTINEL's successor.
-/
theorem addOwner_acyclicity
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (hPreAcyclic : acyclic s)
    (hFreshInList : freshInList s owner) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    acyclic s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Safe.OwnerManagerReach
