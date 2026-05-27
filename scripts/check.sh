#!/usr/bin/env bash
set -euo pipefail

if [[ "${VERITY_BENCHMARK_DOTENVX_LOADED:-}" != "1" ]]; then
  exec "$(dirname "$0")/exec_with_dotenvx.sh" "$0" "$@"
fi

cd "$(dirname "$0")/.."

python3 -m py_compile harness/*.py harness/runners/*.py scripts/check_group_workspaces.py scripts/check_verifier_policy.py scripts/check_run_artifacts.py
python3 -m harness.cli list --suite active --unit group >/dev/null

if python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --dry-run >/tmp/verity-default-run-task-smoke.out; then
  echo "expected default run-task dry-run to fail verification on placeholder proof" >&2
  exit 1
fi
python3 scripts/check_run_artifacts.py "$(tail -1 /tmp/verity-default-run-task-smoke.out)"

if python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --dry-run >/tmp/verity-grok-run-task-smoke.out; then
  echo "expected grok-build run-task dry-run to fail verification on placeholder proof" >&2
  exit 1
fi
python3 scripts/check_run_artifacts.py "$(tail -1 /tmp/verity-grok-run-task-smoke.out)"

python3 scripts/check_group_workspaces.py --suite active
python3 scripts/check_verifier_policy.py
python3 -m harness.sandbox_runner smoke --executor local >/dev/null
python3 -m harness.sandbox_runner smoke --executor podman >/dev/null

python3 scripts/check_reference_solutions.py
python3 scripts/check_axiom_ledger.py
python3 scripts/check_verity_pin_staleness.py --warn-only
python3 scripts/validate_manifests.py
python3 scripts/generate_metadata.py
./scripts/run_all.sh
