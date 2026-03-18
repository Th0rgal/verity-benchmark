# verity-benchmark

Reproducible benchmark scaffold for evaluating Verity-based specification and proof workflows on real protocol slices. The repository is now task-oriented: cases still pin the translated artifact, but benchmark execution and reporting are centered on tasks that reference concrete invariants or specifications.

This repository pins:
- Lean toolchain: `leanprover/lean4:v4.22.0`
- Verity dependency: `Th0rgal/verity@34a6b2b2e91713f870572fef1e1c4b5131812dfb`

Current status:
- Active `cases/`: 4 concrete benchmark cases
- Active `tasks/`: 4 concrete benchmark tasks derived from the current buildable cases
- Buildable `build_green`: 2 cases with compileable Verity translations and frozen simple specs
- Active `scoped`: 2 concrete targets that are pinned but not yet runnable
- `backlog/`: 4 placeholders kept visible without polluting the active suite

Repository layout:
- `Benchmark/`: canonical Lean modules that must compile under `lake build`
- `families/`: family and implementation manifests for benchmark source organization
- `cases/`: active benchmark cases with canonical `case.yaml` manifests and `tasks/*.yaml` benchmark units
- `backlog/`: non-runnable placeholders and intake candidates
- `harness/`: fixed-harness scaffold and task runner
- `schemas/`: machine-readable schemas for manifests and run results
- `benchmark-inventory.json`: generated machine-readable inventory
- `REPORT.md`: generated status report
- `results/`: JSON outputs emitted by the runner scripts
- `scripts/generate_metadata.py`: regenerates the inventory and report from manifests
- `scripts/validate_manifests.py`: validates manifest YAML against the repository schemas
- `scripts/run_task.sh`: agent entrypoint for one benchmark task
- `scripts/run_case.sh`: agent entrypoint for one case
- `scripts/run_all.sh`: agent entrypoint for all active tasks
- `scripts/check.sh`: repo-level metadata and benchmark check

Design choices:
- One folder per benchmark case, with many tasks per case as the intended scaling unit
- Families and implementations are tracked explicitly so source provenance stays stable even as case slices evolve
- One selected contract per project unless scope is still ambiguous
- Frozen specs today, proof targets later; manifest fields already distinguish translation, spec, and proof readiness
- `case.yaml` plus `tasks/*.yaml` are the source of truth for benchmark state
- Stages are intentionally small: `candidate`, `scoped`, `build_green`, `proof_partial`, `proof_complete`
- `build_green` means the Verity slice typechecks today; it does not mean the case is fully proved
- Abstractions and unsupported features are documented explicitly so later papers can reason about abstraction debt and blocked coverage

Manifest model:
- `families/<family>/family.yaml`: semantic grouping and source-language coverage
- `families/<family>/implementations/<impl>/implementation.yaml`: pinned upstream implementation metadata
- `cases/<project>/<case>/case.yaml`: translated slice status, provenance, and abstraction metadata
- `cases/<project>/<case>/tasks/*.yaml`: scored task unit with property class, track, allowed files, and spec/proof targets

Regenerate metadata:

```bash
python3 scripts/generate_metadata.py
```

Run one case:

```bash
./scripts/run_case.sh ethereum/deposit_contract_minimal
```

Run one task:

```bash
./scripts/run_task.sh ethereum/deposit_contract_minimal/deposit_count
```

Run all active cases:

```bash
./scripts/run_all.sh
```

Check metadata and all runnable cases:

```bash
./scripts/check.sh
```
