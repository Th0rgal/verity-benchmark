# owner_manager_reach

Source:
- `safe-global/safe-smart-account` (main)
- commit `a2e19c6aa42a45ceec68057f3fa387f169c5b321`
- file `contracts/base/OwnerManager.sol`

Focus:
- `addOwnerWithThreshold` (linked list head insertion)
- `removeOwner` (linked list node removal)
- `swapOwner` (atomic in-place replacement)
- `setupOwners` (initial list construction — base case)
- Certora `inListReachable` and `reachableInList` invariants from `OwnerReach.spec`
- Acyclicity of the linked list

Model:
- `Benchmark.Cases.Safe.OwnerManagerReach.Contract` defines a Verity contract
  `OwnerManager` with an address-keyed mapping `owners` (slot 0) and a scalar
  `ownerCount` (slot 1). Four functions model the ownership-mutating operations.
- `Specs.lean` defines:
  - `next`, `isChain`, `reachable` (witness-chain based reachability)
  - `inListReachable` — every node with non-zero successor is reachable from SENTINEL
  - `reachableInList` — every reachable node is in the list or is zero
  - `ownerListInvariant` — combined biconditional merging both invariants
  - `acyclic` / `freshInList` — structural properties for eliminating axioms
  - Per-function preservation and establishment specs
- `Proofs.lean` contains:
  - **Proven**: `in_list_reachable` (addOwner preserves inListReachable)
  - **Sorry stubs**: removeOwner, swapOwner, setupOwners preservation for
    inListReachable, ownerListInvariant, and acyclicity (11 proof tasks)

Verification:
- `lake build Benchmark.Cases.Safe.OwnerManagerReach.Compile` checks the
  reference implementation and proofs for the case.
- Files under `Benchmark/Generated/Safe/OwnerManagerReach/Tasks/` are public,
  editable proof templates with holes for benchmark agents to fill.

Out of scope:
- Threshold management (elided — does not affect owners mapping)
- Other OwnerReach.spec invariants (reach_invariant, reach_next, reachCount, etc.)
