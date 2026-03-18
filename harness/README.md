# Task Harness

This directory holds the fixed-harness scaffold for task-oriented benchmark execution.

The benchmark still stores canonical benchmark content in `case.yaml` plus `tasks/*.yaml`,
but execution is centered on a single task at a time. The runner resolves three target
layers for each task:

- translation: a case-level Lean build target
- specification: a declaration exported from a spec module
- proof: an optional proof declaration once a task has a gold or candidate proof target

The shell entrypoints in `scripts/` delegate to `harness/task_runner.py`.

Supported task manifest target fields:

- `spec_target`: Lean module target for the task specification surface
- `proof_target`: Lean module target for the task proof surface when available

If those fields are omitted or not yet ready, the runner derives a specification check from
the case `lean_target` by replacing `.Compile` with `.Specs`, uses `statement_id` as the
task declaration name, and falls back to the case `lean_target` for translation.
