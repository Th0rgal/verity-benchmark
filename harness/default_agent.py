#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib import error, request

from task_runner import ROOT, load_task_record, resolve_task_manifest

AGENT_RESULTS_DIR = ROOT / "results" / "agent_runs"
SCHEMA_PATH = ROOT / "schemas" / "agent-config.schema.json"


@dataclass(frozen=True)
class ResolvedAgentConfig:
    adapter: str
    config_path: str
    base_url: str
    model: str
    api_key: str
    chat_completions_path: str
    system_prompt_files: list[str]
    temperature: float
    max_completion_tokens: int
    headers: dict[str, str]


def load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def type_matches(value: object, expected: str) -> bool:
    if expected == "object":
        return isinstance(value, dict)
    if expected == "array":
        return isinstance(value, list)
    if expected == "string":
        return isinstance(value, str)
    if expected == "integer":
        return isinstance(value, int) and not isinstance(value, bool)
    if expected == "number":
        return isinstance(value, (int, float)) and not isinstance(value, bool)
    if expected == "boolean":
        return isinstance(value, bool)
    if expected == "null":
        return value is None
    raise ValueError(f"unsupported schema type {expected!r}")


def validate(value: object, schema: dict[str, Any], path: str) -> list[str]:
    errors: list[str] = []

    schema_type = schema.get("type")
    if schema_type is not None:
        if isinstance(schema_type, list):
            if not any(type_matches(value, item) for item in schema_type):
                errors.append(f"{path}: expected one of {schema_type}, got {type(value).__name__}")
                return errors
        elif not type_matches(value, schema_type):
            errors.append(f"{path}: expected {schema_type}, got {type(value).__name__}")
            return errors

    if "const" in schema and value != schema["const"]:
        errors.append(f"{path}: expected constant {schema['const']!r}, got {value!r}")

    if "enum" in schema and value not in schema["enum"]:
        errors.append(f"{path}: expected one of {schema['enum']}, got {value!r}")

    if isinstance(value, dict):
        required = schema.get("required", [])
        for key in required:
            if key not in value:
                errors.append(f"{path}: missing required key {key!r}")

        properties = schema.get("properties", {})
        additional = schema.get("additionalProperties", True)
        for key, item in value.items():
            if key in properties:
                errors.extend(validate(item, properties[key], f"{path}.{key}"))
            elif additional is False:
                errors.append(f"{path}: unexpected key {key!r}")
            elif isinstance(additional, dict):
                errors.extend(validate(item, additional, f"{path}.{key}"))

    if isinstance(value, list) and "items" in schema:
        for index, item in enumerate(value):
            errors.extend(validate(item, schema["items"], f"{path}[{index}]"))

    return errors


def validate_config_data(data: object, label: str) -> dict[str, Any]:
    schema = load_json(SCHEMA_PATH)
    if not isinstance(data, dict):
        raise SystemExit(f"{label}: config must decode to an object")
    errors = validate(data, schema, label)
    if errors:
        raise SystemExit("\n".join(errors))
    return data


def load_config(path: Path) -> dict[str, Any]:
    return validate_config_data(load_json(path), str(path.relative_to(ROOT)))


def normalize_string(value: object) -> str | None:
    if value is None:
        return None
    text = str(value).strip()
    return text or None


def resolve_field(config: dict[str, Any], field: str, *, required: bool) -> str | None:
    direct_value = normalize_string(config.get(field))
    if direct_value:
        return direct_value
    env_name = normalize_string(config.get(f"{field}_env"))
    if env_name:
        env_value = normalize_string(os.environ.get(env_name))
        if env_value:
            return env_value
        if required:
            raise SystemExit(f"missing required environment variable {env_name!r} for {field}")
        return None
    if required:
        raise SystemExit(f"missing required config value for {field}")
    return None


def resolve_config(path: Path, *, require_secrets: bool) -> ResolvedAgentConfig:
    config = load_config(path)
    prompt_files = [str(item) for item in config["system_prompt_files"]]
    missing_files = [item for item in prompt_files if not (ROOT / item).is_file()]
    if missing_files:
        raise SystemExit(f"missing system prompt files: {', '.join(missing_files)}")

    headers: dict[str, str] = {}
    raw_headers = config.get("headers", {})
    if isinstance(raw_headers, dict):
        headers = {str(key): str(value) for key, value in raw_headers.items()}

    return ResolvedAgentConfig(
        adapter=str(config["adapter"]),
        config_path=str(path.relative_to(ROOT)),
        base_url=(resolve_field(config, "base_url", required=require_secrets) or "").rstrip("/"),
        model=resolve_field(config, "model", required=require_secrets) or "",
        api_key=resolve_field(config, "api_key", required=require_secrets) or "",
        chat_completions_path=str(config["chat_completions_path"]),
        system_prompt_files=prompt_files,
        temperature=float(config["temperature"]),
        max_completion_tokens=int(config["max_completion_tokens"]),
        headers=headers,
    )


def build_system_prompt(config: ResolvedAgentConfig) -> str:
    sections = []
    for rel_path in config.system_prompt_files:
        path = ROOT / rel_path
        sections.append(f"[{rel_path}]\n{path.read_text(encoding='utf-8').strip()}")
    return "\n\n".join(sections).strip()


def build_user_prompt(task: dict[str, Any]) -> str:
    task_payload = {
        "task_ref": task["task_ref"],
        "task_id": task["task_id"],
        "case_id": task["case_id"],
        "track": task["track"],
        "property_class": task["property_class"],
        "category": task["category"],
        "difficulty": task["difficulty"],
        "statement_id": task["statement_id"],
        "allowed_files": task["allowed_files"],
        "targets": task["targets"],
        "evaluation": task["evaluation"],
        "readiness": task["readiness"],
        "manifest_path": task["manifest_path"],
        "case_manifest_path": task["case_manifest_path"],
    }
    return (
        "You are running the default benchmark agent for verity-benchmark.\n"
        "Treat this as a proof-task benchmark, not an implementation task.\n"
        "Respect the allowed file list.\n\n"
        "Task payload:\n"
        f"{json.dumps(task_payload, indent=2)}\n"
    )


def build_messages(config: ResolvedAgentConfig, task: dict[str, Any]) -> list[dict[str, str]]:
    return [
        {"role": "system", "content": build_system_prompt(config)},
        {"role": "user", "content": build_user_prompt(task)},
    ]


def send_chat_completion(config: ResolvedAgentConfig, messages: list[dict[str, str]]) -> dict[str, Any]:
    url = f"{config.base_url}{config.chat_completions_path}"
    payload = {
        "model": config.model,
        "messages": messages,
        "temperature": config.temperature,
        "max_tokens": config.max_completion_tokens,
    }
    req = request.Request(
        url,
        data=json.dumps(payload).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {config.api_key}",
            "Content-Type": "application/json",
            "User-Agent": "verity-benchmark/0.1",
            **config.headers,
        },
        method="POST",
    )
    try:
        with request.urlopen(req, timeout=120) as response:
            body = response.read().decode("utf-8")
    except error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise SystemExit(f"chat completion request failed with HTTP {exc.code}: {detail}") from exc
    except error.URLError as exc:
        raise SystemExit(f"chat completion request failed: {exc}") from exc
    return json.loads(body)


def extract_text(response: dict[str, Any]) -> str:
    choices = response.get("choices")
    if not isinstance(choices, list) or not choices:
        return ""
    message = choices[0].get("message", {})
    content = message.get("content")
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        parts: list[str] = []
        for item in content:
            if isinstance(item, dict) and item.get("type") == "text":
                text = item.get("text")
                if isinstance(text, str):
                    parts.append(text)
        return "\n".join(parts)
    reasoning_content = message.get("reasoning_content")
    if isinstance(reasoning_content, str):
        return reasoning_content
    return ""


def write_result(task_ref: str, payload: dict[str, Any]) -> Path:
    AGENT_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    result_path = AGENT_RESULTS_DIR / f"{task_ref.replace('/', '__')}.json"
    result_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return result_path


def resolve_task(task_ref: str) -> dict[str, Any]:
    return load_task_record(resolve_task_manifest(task_ref))


def validate_command(config_path: Path) -> int:
    load_config(config_path)
    print(config_path.relative_to(ROOT))
    return 0


def describe_command(config_path: Path) -> int:
    config_data = load_config(config_path)
    config = resolve_config(config_path, require_secrets=False)
    print(
        json.dumps(
            {
                "adapter": config.adapter,
                "config_path": config.config_path,
                "base_url": config.base_url or None,
                "base_url_env": config_data.get("base_url_env"),
                "model": config.model or None,
                "model_env": config_data.get("model_env"),
                "api_key_env": config_data.get("api_key_env"),
                "chat_completions_path": config.chat_completions_path,
                "system_prompt_files": config.system_prompt_files,
                "temperature": config.temperature,
                "max_completion_tokens": config.max_completion_tokens,
                "headers": config.headers,
                "api_key_present": bool(config.api_key),
            },
            indent=2,
        )
    )
    return 0


def prompt_command(config_path: Path, task_ref: str) -> int:
    config = resolve_config(config_path, require_secrets=False)
    task = resolve_task(task_ref)
    payload = {
        "task_ref": task_ref,
        "messages": build_messages(config, task),
    }
    print(json.dumps(payload, indent=2))
    return 0


def run_command(config_path: Path, task_ref: str, dry_run: bool) -> int:
    config = resolve_config(config_path, require_secrets=not dry_run)
    task = resolve_task(task_ref)
    messages = build_messages(config, task)
    timestamp = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    result: dict[str, Any] = {
        "schema_version": 1,
        "task_ref": task_ref,
        "timestamp": timestamp,
        "agent": {
            "adapter": config.adapter,
            "config_path": config.config_path,
            "base_url": config.base_url,
            "model": config.model,
            "chat_completions_path": config.chat_completions_path,
            "system_prompt_files": config.system_prompt_files,
            "temperature": config.temperature,
            "max_completion_tokens": config.max_completion_tokens,
        },
        "messages": messages,
    }
    if dry_run:
        result["dry_run"] = True
        result_path = write_result(task_ref, result)
        print(result_path.relative_to(ROOT))
        return 0

    response = send_chat_completion(config, messages)
    result["response"] = response
    result["response_text"] = extract_text(response)
    result_path = write_result(task_ref, result)
    print(result_path.relative_to(ROOT))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Default benchmark agent adapter")
    subparsers = parser.add_subparsers(dest="command", required=True)

    validate_parser = subparsers.add_parser("validate-config", help="Validate an agent config file")
    validate_parser.add_argument("config")

    describe_parser = subparsers.add_parser("describe", help="Resolve and print a non-secret config summary")
    describe_parser.add_argument("--config", default="harness/default-agent.example.json")

    prompt_parser = subparsers.add_parser("prompt", help="Render the default-agent prompt package for one task")
    prompt_parser.add_argument("task_ref")
    prompt_parser.add_argument("--config", default="harness/default-agent.example.json")

    run_parser = subparsers.add_parser("run", help="Invoke the configured default agent for one task")
    run_parser.add_argument("task_ref")
    run_parser.add_argument("--config", default="harness/default-agent.example.json")
    run_parser.add_argument("--dry-run", action="store_true")

    args = parser.parse_args()

    if args.command == "validate-config":
        return validate_command(ROOT / args.config)
    if args.command == "describe":
        return describe_command(ROOT / args.config)
    if args.command == "prompt":
        return prompt_command(ROOT / args.config, args.task_ref)
    if args.command == "run":
        return run_command(ROOT / args.config, args.task_ref, args.dry_run)

    print(f"unsupported command: {args.command}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
