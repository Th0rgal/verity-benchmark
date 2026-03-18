# Harness Prompt

The benchmark harness assumes a fixed execution contract:

- input unit: one benchmark task
- mutable surface: only files allowed by the task manifest
- selected target kind: proof
- success criterion: the selected proof target resolves and compiles cleanly under Lean

This keeps the benchmark focused on proof obligations over real contract slices.
