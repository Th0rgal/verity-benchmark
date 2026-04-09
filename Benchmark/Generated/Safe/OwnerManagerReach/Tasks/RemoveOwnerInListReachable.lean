import Benchmark.Cases.Safe.OwnerManagerReach.Specs

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
Certora `inListReachable` invariant preservation under `removeOwner`.

After removing `owner` by unlinking it from `prevOwner`, show that every
node with a non-zero successor in the post-state is still reachable from
SENTINEL.

Proof strategy: The removed owner's mapping becomes 0 so it no longer
triggers the invariant. prevOwner now points to owner's old successor,
so chains that went through owner can "skip" it: replace
[... → prevOwner → owner → X → ...] with [... → prevOwner → X → ...].
All other next pointers are unchanged.
-/
theorem removeOwner_inListReachable
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    -- Pre-state invariant
    (hPreInv : inListReachable s)
    -- Acyclicity
    (hAcyclic : acyclic s) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    inListReachable s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Safe.OwnerManagerReach
