# Harness Policy

- Treat `tasks/*.yaml` as the primary execution unit.
- Preserve case-level compatibility fields because Lean translation targets are still defined per case.
- Prefer explicit task targets when present.
- Only execute a proof target when `proof_status` is `partial` or `complete`.
- Fall back from proof to specification to translation, and record the readiness state in the result.
- Emit deterministic task result paths under `results/tasks/`.
