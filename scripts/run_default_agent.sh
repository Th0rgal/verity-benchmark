#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

config_path="${VERITY_BENCHMARK_AGENT_CONFIG:-harness/default-agent.example.json}"
python3 harness/default_agent.py run "$1" --config "$config_path"
