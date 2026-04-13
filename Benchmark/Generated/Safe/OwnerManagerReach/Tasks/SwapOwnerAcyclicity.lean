import Benchmark.Cases.Safe.OwnerManagerReach.Specs

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
swapOwner preserves acyclicity of the owner linked list.

Proof strategy: swapOwner replaces oldOwner with newOwner in-place.
The chain length is preserved. Since newOwner was fresh (not in the
pre-state chain) and oldOwner is removed, no new cycles are introduced.
-/
theorem swapOwner_acyclicity
    (prevOwner oldOwner newOwner : Address) (s : ContractState)
    (hNewNotZero : (newOwner != zeroAddress) = true)
    (hNewNotSentinel : (newOwner != SENTINEL) = true)
    (hNewFresh : (wordToAddress (s.storageMap 0 newOwner) == zeroAddress) = true)
    (hOldNotZero : (oldOwner != zeroAddress) = true)
    (hOldNotSentinel : (oldOwner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == oldOwner) = true)
    (hPreAcyclic : acyclic s)
    (hFresh : freshInList s newOwner) :
    let s' := ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd
    acyclic s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Safe.OwnerManagerReach
