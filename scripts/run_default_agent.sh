#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ -n "${VERITY_BENCHMARK_AGENT_PROFILE:-}" && -n "${VERITY_BENCHMARK_AGENT_CONFIG:-}" ]]; then
  echo "set either VERITY_BENCHMARK_AGENT_PROFILE or VERITY_BENCHMARK_AGENT_CONFIG, not both" >&2
  exit 1
fi

if [[ -n "${VERITY_BENCHMARK_AGENT_PROFILE:-}" ]]; then
  python3 harness/default_agent.py run "$1" --profile "$VERITY_BENCHMARK_AGENT_PROFILE"
elif [[ -n "${VERITY_BENCHMARK_AGENT_CONFIG:-}" ]]; then
  python3 harness/default_agent.py run "$1" --config "$VERITY_BENCHMARK_AGENT_CONFIG"
else
  python3 harness/default_agent.py run "$1" --profile default
fi
