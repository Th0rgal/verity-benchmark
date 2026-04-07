# owner_manager_reach

Source:
- `safe-global/safe-smart-account` (main)
- file `contracts/base/OwnerManager.sol`

Focus:
- `addOwnerWithThreshold` (linked list head insertion)
- Certora `inListReachable` invariant from `OwnerReach.spec`

Model:
- `Benchmark.Cases.Safe.OwnerManagerReach.Contract` defines a Verity contract
  `OwnerManager` with an address-keyed mapping `owners` (slot 0) and a scalar
  `ownerCount` (slot 1). The `addOwner` function models the linked list
  insertion: it checks the owner is valid (non-zero, non-sentinel, fresh),
  then splices the new owner at the head of the list.
- `Specs.lean` defines `next`, `isChain`, `reachable` (witness-chain based),
  and `in_list_reachable_spec` matching the Certora invariant.
- `Proofs.lean` proves invariant preservation under `addOwner` by:
  1. Characterizing the post-state storageMap (`addOwner_storageMap`)
  2. Deriving the next-pointer update (`addOwner_next_eq`)
  3. Lifting pre-state chains to the post-state (`isChain_lift`)
  4. Constructing post-state reachability via chain prepending

Verification:
- `lake build Benchmark.Cases.Safe.OwnerManagerReach.Compile` checks the
  reference implementation and proofs for the case.
- Files under `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/` are public,
  editable proof templates with holes for benchmark agents to fill.

Out of scope:
- Threshold management
- removeOwner, swapOwner
- setupOwners (initial setup)
- Other OwnerReach.spec invariants (headReachable, isOwnerMapping, etc.)
