<h1 align="center">Verity Benchmark</h1>

<p align="center">
  <strong>Measuring AI agents at formally verifying smart contracts in Lean 4.</strong>
</p>

<p align="center">
  <a href="https://veritylang.com"><img src="https://img.shields.io/badge/docs-veritylang.com-0a7d7d.svg" alt="Verity documentation"></a>
  <a href="https://github.com/lfglabs-dev/verity-benchmark"><img src="https://img.shields.io/badge/built%20with-Lean%204-blueviolet.svg" alt="Built with Lean 4"></a>
  <a href="https://github.com/lfglabs-dev/verity-benchmark/actions"><img src="https://img.shields.io/github/actions/workflow/status/lfglabs-dev/verity-benchmark/check.yml?label=check" alt="Check"></a>
</p>

<p align="center">
  <a href="https://veritylang.com">Documentation</a>
  &nbsp;·&nbsp;
  <a href="https://github.com/lfglabs-dev/verity">Verity compiler</a>
  &nbsp;·&nbsp;
  <a href="https://lfglabs.dev/research/verity-benchmark">Research note</a>
  &nbsp;·&nbsp;
  <a href="https://lfglabs.dev/papers/verity.pdf">Paper (PDF)</a>
</p>

---

## What is this?

**Verity Benchmark** is an open evaluation suite that measures how well AI agents can produce **formal proofs** of smart contract correctness in [Lean 4](https://lean-lang.org/), on top of the [Verity](https://github.com/lfglabs-dev/verity) formally verified smart contract compiler. Cases are drawn from real-world Ethereum protocols (Ethereum deposit contract, Lido, Nexus Mutual, Kleros, Paladin, Damn Vulnerable DeFi).

[Verity](https://veritylang.com) lets you write smart contracts, state what they should do, prove correctness, and compile to EVM bytecode with machine-checked proofs that compilation preserves semantics. This benchmark is an initiative made in partnership with the **Ethereum Foundation** and various protocols of the ecosystem. Full documentation lives at [**veritylang.com**](https://veritylang.com); the team behind it is [**LFG Labs**](https://lfglabs.dev).

Each benchmark task gives an agent:
- A fixed contract implementation
- A fixed formal specification
- One editable proof file with a single theorem to prove

The agent must produce a valid Lean proof. No placeholders (`sorry`, `admit`, `axiom`) allowed.

---

## Benchmark suite

6 cases, 30 tasks, drawn from real-world contracts:

| Case | Source | Tasks |
|------|--------|-------|
| `ethereum/deposit_contract_minimal` | Ethereum deposit contract | 5 |
| `lido/vaulthub_locked` | Lido VaultHub | 5 |
| `nexus_mutual/ramm_price_band` | Nexus Mutual RAMM | 4 |
| `kleros/sortition_trees` | Kleros sortition module | 6 |
| `paladin_votes/stream_recovery_claim_usdc` | Paladin Votes | 5 |
| `damn_vulnerable_defi/side_entrance` | Damn Vulnerable DeFi | 5 |

Most cases include a reference proof (hidden from the agent during benchmarking) that validates the task is solvable.

---

## Running the benchmark

### Verify reference proofs

```bash
# Single task
./scripts/run_task.sh ethereum/deposit_contract_minimal/deposit_count

# All tasks in a case
./scripts/run_case.sh ethereum/deposit_contract_minimal

# Full suite
./scripts/run_all.sh
```

### Run with the built-in harness

The benchmark ships with an agent harness that supports any OpenAI-compatible API. In `interactive` mode, it exposes Lean-specific tools to the agent:

| Tool | Purpose |
|------|---------|
| `read_public_file` | Read implementation and spec files |
| `write_editable_proof` | Write the proof file |
| `run_lean_check` | Type-check the proof, with structured error feedback and repair hints |
| `inspect_lean_goals` | Inspect open proof goals at hole sites |
| `try_tactic_at_hole` | Test a tactic at proof holes without committing |
| `search_public_defs` | Search definitions across implementation and spec files |

```bash
# Run a single task with the built-in agent
./scripts/run_default_agent.sh lido/vaulthub_locked/locked_funds_solvency

# Run a full case
./scripts/run_default_agent_case.sh lido/vaulthub_locked

# Run the full suite
./scripts/run_default_agent_all.sh
```

To test a different model, configure the agent profile:

```bash
python3 harness/default_agent.py profiles
python3 harness/default_agent.py describe --profile openai-compatible
```

### Use a custom harness

The benchmark also supports custom agent harnesses via an external command adapter. The evaluation contract stays the same: fixed input files, one editable proof, one required theorem.

```bash
./scripts/run_custom_agent.sh ethereum/deposit_contract_minimal/deposit_count
./scripts/run_custom_agent_case.sh ethereum/deposit_contract_minimal
./scripts/run_custom_agent_all.sh
```

### Benchmark matrix

Run multiple models/harnesses in parallel and compare results:

```bash
python3 scripts/run_benchmark_matrix.py start
python3 scripts/run_benchmark_matrix.py status
python3 scripts/run_benchmark_matrix.py wait
```

---

## Project structure

```
verity-benchmark/
├── Benchmark/
│   ├── Cases/           # Reference proofs (hidden from agents)
│   └── Generated/       # Public proof templates
├── cases/               # Task manifests and contract sources
├── harness/             # Agent runner, tools, and evaluation
├── scripts/             # CLI entry points
├── schemas/             # JSON schemas for results
└── results/             # Run artifacts
```

---

## Documentation

| Document | Description |
|----------|-------------|
| [harness/README.md](./harness/README.md) | Harness internals and agent integration |
| [docs/architecture/task-api.md](./docs/architecture/task-api.md) | Task contract and manifest format |
| [docs/architecture/runtime-modes.md](./docs/architecture/runtime-modes.md) | Runtime modes (strict, interactive, custom) |

<!-- BENCHMARK_MATRIX:START -->
## Benchmark Results

Run `python3 scripts/run_benchmark_matrix.py render` after the matrix finishes to refresh this section.
<!-- BENCHMARK_MATRIX:END -->
