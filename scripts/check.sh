#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
python3 harness/default_agent.py validate-config harness/default-agent.example.json
python3 harness/default_agent.py run ethereum/deposit_contract_minimal/deposit_count --config harness/default-agent.example.json --dry-run
python3 scripts/validate_manifests.py
python3 scripts/generate_metadata.py
./scripts/run_all.sh
