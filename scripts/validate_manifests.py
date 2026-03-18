#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path
import sys

import yaml

ROOT = Path(__file__).resolve().parent.parent
SCHEMA_ROOT = ROOT / "schemas"


def load_yaml(path: Path) -> object:
    with path.open(encoding="utf-8") as handle:
        return yaml.safe_load(handle)


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


def validate(value: object, schema: dict, path: str) -> list[str]:
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


def collect_paths(pattern: str) -> list[Path]:
    return sorted(ROOT.glob(pattern))


def main() -> int:
    schema_files = {
        "family": load_json(SCHEMA_ROOT / "family.schema.json"),
        "implementation": load_json(SCHEMA_ROOT / "implementation.schema.json"),
        "case": load_json(SCHEMA_ROOT / "case.schema.json"),
        "task": load_json(SCHEMA_ROOT / "task.schema.json"),
    }

    errors: list[str] = []
    family_manifests = collect_paths("families/*/family.yaml")
    implementation_manifests = collect_paths("families/*/implementations/*/implementation.yaml")
    case_manifests = collect_paths("cases/*/*/case.yaml") + collect_paths("backlog/*/*/case.yaml")
    task_manifests = collect_paths("cases/*/*/tasks/*.yaml")

    families: dict[str, dict] = {}
    implementations: dict[tuple[str, str], dict] = {}
    cases: dict[str, dict] = {}

    for path in family_manifests:
        data = load_yaml(path)
        errors.extend(validate(data, schema_files["family"], str(path.relative_to(ROOT))))
        if isinstance(data, dict):
            family_id = data.get("family_id")
            if isinstance(family_id, str):
                families[family_id] = data

    for path in implementation_manifests:
        data = load_yaml(path)
        errors.extend(validate(data, schema_files["implementation"], str(path.relative_to(ROOT))))
        if isinstance(data, dict):
            family_id = data.get("family_id")
            implementation_id = data.get("implementation_id")
            if isinstance(family_id, str) and isinstance(implementation_id, str):
                implementations[(family_id, implementation_id)] = data

    for path in case_manifests:
        data = load_yaml(path)
        rel = str(path.relative_to(ROOT))
        errors.extend(validate(data, schema_files["case"], rel))
        if not isinstance(data, dict):
            continue
        project = data.get("project")
        case_id = data.get("case_id")
        family_id = data.get("family_id")
        implementation_id = data.get("implementation_id")
        if isinstance(project, str) and isinstance(case_id, str):
            full_case_id = f"{project}/{case_id}"
            cases[full_case_id] = data
            if family_id != project:
                errors.append(f"{rel}: family_id must match project for current layout")
            if not isinstance(family_id, str) or family_id not in families:
                errors.append(f"{rel}: unknown family_id {family_id!r}")
            if not isinstance(family_id, str) or not isinstance(implementation_id, str):
                errors.append(f"{rel}: implementation reference is incomplete")
            elif (family_id, implementation_id) not in implementations:
                errors.append(f"{rel}: unknown implementation {(family_id, implementation_id)!r}")

    for path in task_manifests:
        data = load_yaml(path)
        rel = str(path.relative_to(ROOT))
        errors.extend(validate(data, schema_files["task"], rel))
        if not isinstance(data, dict):
            continue
        case_id = data.get("case_id")
        family_id = data.get("family_id")
        implementation_id = data.get("implementation_id")
        if not isinstance(case_id, str) or case_id not in cases:
            errors.append(f"{rel}: unknown case_id {case_id!r}")
        if not isinstance(family_id, str) or family_id not in families:
            errors.append(f"{rel}: unknown family_id {family_id!r}")
        if not isinstance(family_id, str) or not isinstance(implementation_id, str):
            errors.append(f"{rel}: implementation reference is incomplete")
        elif (family_id, implementation_id) not in implementations:
            errors.append(f"{rel}: unknown implementation {(family_id, implementation_id)!r}")
        allowed_files = data.get("allowed_files")
        if isinstance(allowed_files, list):
            for allowed in allowed_files:
                allowed_path = ROOT / allowed
                if not allowed_path.exists():
                    errors.append(f"{rel}: allowed_files entry does not exist: {allowed}")

    for family_id, data in families.items():
        for case_id in data["case_ids"]:
            if case_id not in cases:
                errors.append(f"families/{family_id}/family.yaml: missing case reference {case_id}")
        for implementation_id in data["implementation_ids"]:
            if (family_id, implementation_id) not in implementations:
                errors.append(
                    f"families/{family_id}/family.yaml: missing implementation reference {implementation_id}"
                )

    if errors:
        print("manifest validation failed", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print(
        "validated"
        f" {len(family_manifests)} family,"
        f" {len(implementation_manifests)} implementation,"
        f" {len(case_manifests)} case,"
        f" {len(task_manifests)} task manifests"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
