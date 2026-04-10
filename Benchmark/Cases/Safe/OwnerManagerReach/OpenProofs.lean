import Benchmark.Cases.Safe.OwnerManagerReach.Specs

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/-!
This module holds theorem skeletons for tasks that are translated but not yet
part of the compiled reference-proof set. The complete reference module is
`Proofs.lean`; editable agent-facing stubs live under `Benchmark/Generated/...`.

The following theorems have been fully proven in `Proofs.lean` and removed
from this file:
  - `removeOwner_inListReachable`   (Part 5)
  - `swapOwner_inListReachable`     (Part 7)
  - `setupOwners_inListReachable`   (Part 2)
  - `addOwner_ownerListInvariant`   (Part 8)
  - `setupOwners_ownerListInvariant`(Part 3)
  - `addOwner_acyclicity`           (Part 1)
  - `removeOwner_acyclicity`        (Part 4)
  - `swapOwner_acyclicity`          (Part 6)
  - `setupOwners_acyclicity`        (Part 2)

The remaining stubs below are fully proven in `Proofs.lean` (Part 8).
They require additional hypotheses beyond the original signatures,
documented inline. The `sorry` stubs here are kept as agent-facing
task templates.
-/

/-! ### removeOwner_ownerListInvariant

  Fully proven in `Proofs.lean` (Part 8). Additional hypotheses beyond the
  original Solidity contract requirements:
  - `uniquePredecessor s`: each non-zero node has at most one non-zero predecessor
  - `owner ≠ prevOwner`: excludes degenerate self-removal
  - `prevOwner ≠ zeroAddress`: predecessor is a valid list node
  - `next s owner ≠ owner`: no self-loop
  - `next s zeroAddress = zeroAddress`: zero address is inert
-/
theorem removeOwner_ownerListInvariant
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    (hOwnerInList : next s owner ≠ zeroAddress)
    (hPreInv : ownerListInvariant s)
    (hAcyclic : acyclic s)
    (hUniquePred : uniquePredecessor s)
    (hOwnerNePrev : owner ≠ prevOwner)
    (hPrevNZ : prevOwner ≠ zeroAddress)
    (hNoSelfLoop : next s owner ≠ owner)
    (hZeroInert : next s zeroAddress = zeroAddress) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    ownerListInvariant s' := by
  sorry

/-! ### swapOwner_ownerListInvariant

  Fully proven in `Proofs.lean` (Part 8). Additional hypotheses:
  - `uniquePredecessor s`: each non-zero node has at most one non-zero predecessor
  - `prevOwner ≠ zeroAddress`: predecessor is a valid list node
  - `next s oldOwner ≠ oldOwner`: no self-loop at the swapped node
  - `next s zeroAddress = zeroAddress`: zero address is inert
-/
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
    (hUniquePred : uniquePredecessor s)
    (hFresh : freshInList s newOwner)
    (hPrevNZ : prevOwner ≠ zeroAddress)
    (hNoSelfLoop : next s oldOwner ≠ oldOwner)
    (hZeroInert : next s zeroAddress = zeroAddress) :
    let s' := ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd
    ownerListInvariant s' := by
  sorry

end Benchmark.Cases.Safe.OwnerManagerReach
