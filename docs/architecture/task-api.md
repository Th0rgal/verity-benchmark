# Task API Architecture Note

## Current model

The repository stores benchmark tasks under `cases/*/*/tasks/*.yaml`. Each task is a
proof target with an explicit Lean module and declaration to check.

## Target model

The intended architecture is:

- `family`: semantic grouping across protocols and repositories
- `implementation`: pinned upstream codebase identity
- `case`: curation and provenance unit
- `task`: benchmark API and evaluation unit
- `source_ref`: pinned source snapshot reference used for reproducibility

`case` remains the place where we record why a slice exists, what was translated, and
what abstractions were introduced. `task` is the public contract that an evaluator
consumes.

## Why task is the benchmark API

A benchmark score is attached to a concrete property, not to a folder. The task
manifest is now the place that explicitly declares:

- which pinned source snapshot the task belongs to via `source_ref`
- which artifacts are in scope via `allowed_files`
- which evaluation engine is used via `evaluation_engine`
- which proof module is executed via `evaluation_target`
- which proof declaration must exist via `evaluation_declaration`

This removes hidden execution semantics from runner conventions. A task can still share
provenance with its parent case, but it no longer relies on the runner to guess the
evaluation contract.

## Case vs Task vs Source Snapshot

- `case` is the curation and abstraction boundary. It records selected functions,
  abstraction notes, upstream origin, and the translated Lean target.
- `task` is the scored unit. It packages the property class, task interface, artifacts
  in scope, and explicit evaluation contract.
- `source_ref` is the reproducibility unit. In the current repo it is a pinned string
  of the form `<repo>@<commit>:<path>`.

This is intentionally separate from local workspace paths. Evaluation should depend on
the pinned source reference and declared task artifacts, not on whichever checkout
happens to be lying around on a contributor machine.

## Source snapshots and symlinks

This repository does not use symlinks as a canonical architecture.

The canonical mechanism is the pinned `source_ref` recorded in manifests. A future
materialization step can fetch or vendor those snapshots into a local cache, but that
would be an implementation convenience layered on top of the manifest contract.

If symlinks are ever generated for local ergonomics, they should remain optional and
derived. They must not become the benchmark's source of truth.
