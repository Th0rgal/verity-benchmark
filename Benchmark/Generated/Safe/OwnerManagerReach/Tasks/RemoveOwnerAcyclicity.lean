import Benchmark.Cases.Safe.OwnerManagerReach.Specs

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
removeOwner preserves acyclicity of the owner linked list.

Proof strategy: Removing a node shortens the chain by one element.
If SENTINEL was not in any pre-state chain past the head, and removing
a node only splices out one element (without introducing SENTINEL),
SENTINEL remains absent from all post-state chains.
-/
theorem removeOwner_acyclicity
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    (hPreAcyclic : acyclic s) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    acyclic s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Safe.OwnerManagerReach
