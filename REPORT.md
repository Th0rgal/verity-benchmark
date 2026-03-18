# Benchmark report

This report is generated from the benchmark manifests.

## Summary

- Families: 7
- Implementations: 8
- Active cases: 4
- Buildable active cases: 2
- Active tasks: 4
- Backlog cases: 4

## Buildable active cases

### `ethereum/deposit_contract_minimal`
- Family / implementation: `ethereum` / `deposit_contract`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`not_started`
- Lean target: `Benchmark.Cases.Ethereum.DepositContractMinimal.Compile`
- Selected functions: `deposit`
- Source artifact: `deposit_contract/contracts/validator_registration.v.py`
- Notes: Counter-oriented slice of the deposit path. Merkle tree, SSZ hashing, and log emission are omitted so the benchmark can focus on threshold-driven state updates.

### `paladin_votes/stream_recovery_claim_usdc`
- Family / implementation: `paladin_votes` / `stream_recovery_claim`
- Stage: `build_green`
- Status dimensions: translation=`translated`, spec=`frozen`, proof=`not_started`
- Lean target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Compile`
- Selected functions: `claimUsdc`, `_claimUsdc`
- Source artifact: `src/StreamRecoveryClaim.sol`
- Notes: Single-round accounting slice of the USDC claim path. Merkle verification is abstracted as a boolean witness and token transfer side effects are omitted.

## Non-buildable active cases

### `ethereum/beacon_roots_predeploy`
- Family / implementation: `ethereum` / `beacon_roots_predeploy`
- Stage: `scoped`
- Status dimensions: translation=`blocked`, spec=`draft`, proof=`blocked`
- Failure reason: `missing_implementation_artifact`
- Selected functions: `get`, `set`
- Source artifact: `EIPS/eip-4788.md`
- Notes: Candidate selected, but the benchmark currently lacks a pinned implementation artifact beyond the EIP text.

### `zama/erc7984`
- Family / implementation: `zama` / `openzeppelin_confidential_contracts`
- Stage: `scoped`
- Status dimensions: translation=`blocked`, spec=`blocked`, proof=`blocked`
- Failure reason: `missing_verity_feature`
- Selected functions: `confidentialTransfer`, `confidentialTransferFrom`
- Source artifact: `contracts/token/ERC7984/ERC7984.sol`
- Notes: Selected as requested, but blocked because the contract depends on encrypted euint64 values and FHE-specific runtime semantics that are not benchmarked in this v1 scaffold.

## Active tasks

### `ethereum/deposit_contract_minimal/chain_start_threshold`
- Track / property class: `proof-only` / `threshold_activation`
- Readiness: translation=`ready`, spec=`ready`, proof=`planned`
- Statement id: `deposit_starts_chain_at_threshold_spec`
- Spec target: `Benchmark.Cases.Ethereum.DepositContractMinimal.Specs`

### `ethereum/deposit_contract_minimal/deposit_count`
- Track / property class: `proof-only` / `monotonic_counter`
- Readiness: translation=`ready`, spec=`ready`, proof=`planned`
- Statement id: `deposit_increments_deposit_count_spec`
- Spec target: `Benchmark.Cases.Ethereum.DepositContractMinimal.Specs`

### `paladin_votes/stream_recovery_claim_usdc/claim_marks_user`
- Track / property class: `proof-only` / `authorization_state`
- Readiness: translation=`ready`, spec=`ready`, proof=`planned`
- Statement id: `claimUsdc_marks_claimed_spec`
- Spec target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs`

### `paladin_votes/stream_recovery_claim_usdc/no_overclaim`
- Track / property class: `proof-only` / `accounting_bound`
- Readiness: translation=`ready`, spec=`ready`, proof=`planned`
- Statement id: `claimUsdc_preserves_round_bound_spec`
- Spec target: `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs`

## Backlog

### `kleros/placeholder`
- Family / implementation: `kleros` / `kleros_v2`
- Stage: `candidate`
- Status dimensions: translation=`not_started`, spec=`not_started`, proof=`blocked`
- Failure reason: `selection_pending`
- Source artifact: `TBD`
- Notes: Waiting for protocol-side contract/function selection.

### `nexus_mutual/placeholder`
- Family / implementation: `nexus_mutual` / `smart_contracts`
- Stage: `candidate`
- Status dimensions: translation=`not_started`, spec=`not_started`, proof=`blocked`
- Failure reason: `selection_pending`
- Source artifact: `TBD`
- Notes: Waiting for protocol-side invariant and target contract selection.

### `unlink_xyz/placeholder`
- Family / implementation: `unlink_xyz` / `monorepo`
- Stage: `candidate`
- Status dimensions: translation=`blocked`, spec=`not_started`, proof=`blocked`
- Failure reason: `upstream_unavailable`
- Source artifact: `TBD`
- Notes: Referenced repository was not resolvable during setup, so no candidate contract was pinned.

### `usual/placeholder`
- Family / implementation: `usual` / `private_repo`
- Stage: `candidate`
- Status dimensions: translation=`blocked`, spec=`not_started`, proof=`blocked`
- Failure reason: `private_access`
- Source artifact: `TBD`
- Notes: Pending private repository access and target selection.

## Commands

- Validate manifests: `python3 scripts/validate_manifests.py`
- Regenerate metadata: `python3 scripts/generate_metadata.py`
- Run one task: `./scripts/run_task.sh <project/case_id/task_id>`
- Run one case: `./scripts/run_case.sh <project/case_id>`
- Run active suite: `./scripts/run_all.sh`
- Run repo check: `./scripts/check.sh`
