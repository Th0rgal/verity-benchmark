# Harness Prompt

The benchmark harness assumes a fixed execution contract:

- input unit: one benchmark task
- mutable surface: only files allowed by the task manifest
- preferred target order: proof, then specification, then translation fallback
- success criterion: the selected target resolves and compiles cleanly under Lean

This keeps the current dataset executable while the benchmark grows from frozen
specification targets into proof-producing tasks over real contracts.
