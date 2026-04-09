import Benchmark.Cases.Safe.OwnerManagerReach.Specs

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/-!
This module holds theorem skeletons for tasks that are translated but not yet
part of the compiled reference-proof set. The complete reference module is
`Proofs.lean`; editable agent-facing stubs live under `Benchmark/Generated/...`.
-/

theorem removeOwner_inListReachable
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    -- The removed owner must have a non-zero successor (i.e. be in the list).
    -- Without this, removing the sole remaining owner would make
    -- owners[SENTINEL] = 0, violating inListReachable.
    (hOwnerInList : next s owner ≠ zeroAddress)
    (hPreInv : inListReachable s)
    (hAcyclic : acyclic s)
    (hStrongAcyclic : stronglyAcyclic s) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    inListReachable s' := by
  sorry

theorem swapOwner_inListReachable
    (prevOwner oldOwner newOwner : Address) (s : ContractState)
    (hNewNotZero : (newOwner != zeroAddress) = true)
    (hNewNotSentinel : (newOwner != SENTINEL) = true)
    (hNewFresh : (wordToAddress (s.storageMap 0 newOwner) == zeroAddress) = true)
    (hOldNotZero : (oldOwner != zeroAddress) = true)
    (hOldNotSentinel : (oldOwner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == oldOwner) = true)
    (hOldNePrev : oldOwner ≠ prevOwner)
    (hPreInv : inListReachable s)
    (hAcyclic : acyclic s)
    (hStrongAcyclic : stronglyAcyclic s)
    (hFresh : freshInList s newOwner) :
    let s' := ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd
    inListReachable s' := by
  sorry

theorem setupOwners_inListReachable
    (owner1 owner2 owner3 : Address) (s : ContractState)
    (h1NZ : (owner1 != zeroAddress) = true)
    (h1NS : (owner1 != SENTINEL) = true)
    (h2NZ : (owner2 != zeroAddress) = true)
    (h2NS : (owner2 != SENTINEL) = true)
    (h3NZ : (owner3 != zeroAddress) = true)
    (h3NS : (owner3 != SENTINEL) = true)
    (h12 : (owner1 != owner2) = true)
    (h13 : (owner1 != owner3) = true)
    (h23 : (owner2 != owner3) = true)
    -- Clean pre-state: no pre-existing owner links.
    -- Without this, stale mappings from a prior state could leave nodes with
    -- non-zero successors that are unreachable from SENTINEL after setup.
    (hClean : ∀ addr : Address, s.storageMap 0 addr = 0) :
    let s' := ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
    inListReachable s' := by
  sorry

theorem addOwner_ownerListInvariant
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (hPreInv : ownerListInvariant s)
    (hAcyclic : acyclic s)
    (hFreshInList : freshInList s owner) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    ownerListInvariant s' := by
  sorry

theorem removeOwner_ownerListInvariant
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    (hOwnerInList : next s owner ≠ zeroAddress)
    (hPreInv : ownerListInvariant s)
    (hAcyclic : acyclic s) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    ownerListInvariant s' := by
  sorry

theorem swapOwner_ownerListInvariant
    (prevOwner oldOwner newOwner : Address) (s : ContractState)
    (hNewNotZero : (newOwner != zeroAddress) = true)
    (hNewNotSentinel : (newOwner != SENTINEL) = true)
    (hNewFresh : (wordToAddress (s.storageMap 0 newOwner) == zeroAddress) = true)
    (hOldNotZero : (oldOwner != zeroAddress) = true)
    (hOldNotSentinel : (oldOwner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == oldOwner) = true)
    (hOldNePrev : oldOwner ≠ prevOwner)
    (hPreInv : ownerListInvariant s)
    (hAcyclic : acyclic s)
    (hFresh : freshInList s newOwner) :
    let s' := ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd
    ownerListInvariant s' := by
  sorry

theorem setupOwners_ownerListInvariant
    (owner1 owner2 owner3 : Address) (s : ContractState)
    (h1NZ : (owner1 != zeroAddress) = true)
    (h1NS : (owner1 != SENTINEL) = true)
    (h2NZ : (owner2 != zeroAddress) = true)
    (h2NS : (owner2 != SENTINEL) = true)
    (h3NZ : (owner3 != zeroAddress) = true)
    (h3NS : (owner3 != SENTINEL) = true)
    (h12 : (owner1 != owner2) = true)
    (h13 : (owner1 != owner3) = true)
    (h23 : (owner2 != owner3) = true)
    (hClean : ∀ addr : Address, s.storageMap 0 addr = 0) :
    let s' := ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
    ownerListInvariant s' := by
  sorry

theorem addOwner_acyclicity
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (hPreAcyclic : acyclic s)
    (hFreshInList : freshInList s owner) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    acyclic s' := by
  sorry

theorem removeOwner_acyclicity
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    (hOwnerInList : next s owner ≠ zeroAddress)
    (hPreAcyclic : acyclic s) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    acyclic s' := by
  sorry

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
  sorry

theorem setupOwners_acyclicity
    (owner1 owner2 owner3 : Address) (s : ContractState)
    (h1NZ : (owner1 != zeroAddress) = true)
    (h1NS : (owner1 != SENTINEL) = true)
    (h2NZ : (owner2 != zeroAddress) = true)
    (h2NS : (owner2 != SENTINEL) = true)
    (h3NZ : (owner3 != zeroAddress) = true)
    (h3NS : (owner3 != SENTINEL) = true)
    (h12 : (owner1 != owner2) = true)
    (h13 : (owner1 != owner3) = true)
    (h23 : (owner2 != owner3) = true)
    (hClean : ∀ addr : Address, s.storageMap 0 addr = 0) :
    let s' := ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
    acyclic s' := by
  sorry

end Benchmark.Cases.Safe.OwnerManagerReach
