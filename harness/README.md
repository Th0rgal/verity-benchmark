# Task Harness

This directory holds the fixed-harness scaffold for task-oriented benchmark execution.

Execution is centered on a single task at a time. The task manifest is the execution
contract, and the runner consumes its explicit evaluation fields instead of deriving the
public benchmark interface from case-level conventions.

Supported evaluation layers:

- translation: build a translated Lean module
- specification: build a spec module and `#check` the declared statement
- proof: build a proof module and `#check` the declared proof/export

The shell entrypoints in `scripts/` delegate to `harness/task_runner.py`.

The default benchmark agent now has its own explicit entrypoint:

- `scripts/run_default_agent.sh <task_ref>` invokes the default-agent runner for one task
- `scripts/run_default_agent_case.sh <project/case_id>` invokes the same path for each task in one case
- `scripts/run_default_agent_all.sh` invokes the same path for all active tasks
- `harness/agent_runner.py` is the first-class runner for task, case, and suite default-agent execution
- bundled reusable profiles live in `harness/agents/*.json`
- the default profile is `default`, and the proxy example profile is `openai-proxy-fast`
- the current adapter is `openai_compatible`
- credentials and endpoint selection are injected through env vars instead of being hard-coded
- the default-agent run artifact is schema-backed by `schemas/agent-run.schema.json`
- aggregated case/suite agent-run status is written to `results/agent_summary.json`

Default OpenAI-compatible env contract:

- `VERITY_BENCHMARK_AGENT_BASE_URL`
- `VERITY_BENCHMARK_AGENT_MODEL`
- `VERITY_BENCHMARK_AGENT_API_KEY`

Bundled profile contract:

- `default`: expects all three env vars above
- `openai-proxy-fast`: pins base URL to `https://agent-backend.thomas.md/v1` and model to `builtin/fast`, and only requires `VERITY_BENCHMARK_AGENT_API_KEY`

Optional config-only extensions for OpenAI-compatible backends:

- `models_path`: model-discovery path used by `probe`
- `header_envs`: map of HTTP header name to env var for proxy-specific auth/routing
- `extra_body`: extra JSON merged into the chat-completions request body
- `request_timeout_seconds`: request timeout for both probe and run

Useful commands:

- `python3 harness/agent_runner.py list --suite active`
- `python3 harness/default_agent.py profiles`
- `python3 harness/default_agent.py validate-config harness/agents/default.json`
- `python3 harness/default_agent.py describe --profile default`
- `python3 harness/default_agent.py probe --profile openai-proxy-fast --ensure-model`
- `python3 harness/default_agent.py prompt ethereum/deposit_contract_minimal/deposit_count --profile default`
- `VERITY_BENCHMARK_AGENT_PROFILE=openai-proxy-fast ./scripts/run_default_agent.sh ethereum/deposit_contract_minimal/deposit_count`
- `VERITY_BENCHMARK_AGENT_PROFILE=openai-proxy-fast ./scripts/run_default_agent_case.sh ethereum/deposit_contract_minimal`
- `VERITY_BENCHMARK_AGENT_PROFILE=openai-proxy-fast ./scripts/run_default_agent_all.sh`

Supported task manifest interface fields:

- `source_ref`: pinned upstream source reference for reproducibility
- `task_interface_version`: version of the task execution contract
- `spec_target`: Lean module target for the task specification surface
- `proof_target`: Lean module target for the task proof surface when available
- `evaluation_engine`: currently `lean_build`
- `evaluation_target_kind`: one of `translation`, `spec`, `proof`
- `evaluation_target`: the module passed to `lake build`
- `evaluation_declaration`: declaration that must exist for `spec` and `proof` tasks

`case.yaml` still carries curation and provenance metadata, but it is no longer the
canonical description of how a task is executed.
