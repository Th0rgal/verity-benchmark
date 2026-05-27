#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 -m harness.cli run-suite --harness grok-build "$@"
