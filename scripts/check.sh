#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
python3 harness/default_agent.py profiles
python3 harness/default_agent.py validate-config harness/agents/default.json
python3 harness/default_agent.py validate-config harness/agents/openai-proxy-fast.json
python3 harness/default_agent.py run ethereum/deposit_contract_minimal/deposit_count --profile default --dry-run
python3 scripts/validate_manifests.py
python3 scripts/generate_metadata.py
./scripts/run_all.sh
