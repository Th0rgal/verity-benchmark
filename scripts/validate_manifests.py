#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path
import sys

from manifest_utils import load_manifest_data

ROOT = Path(__file__).resolve().parent.parent
SCHEMA_ROOT = ROOT / "schemas"
PROOF_FAMILIES = {
    "functional_correctness",
    "state_preservation_local_effects",
    "authorization_enablement",
    "protocol_transition_correctness",
    "refinement_equivalence",
}


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


def load_manifest(path: Path) -> dict:
    data = load_manifest_data(path)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: manifest must decode to an object")
    return data


def expected_source_ref(data: dict) -> str | None:
    upstream_repo = data.get("upstream_repo")
    upstream_commit = data.get("upstream_commit")
    original_contract_path = data.get("original_contract_path")
    if not all(isinstance(item, str) and item for item in (upstream_repo, upstream_commit, original_contract_path)):
        return None
    return f"{upstream_repo}@{upstream_commit}:{original_contract_path}"


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
    task_manifests = collect_paths("cases/*/*/tasks/*.yaml") + collect_paths("backlog/*/*/tasks/*.yaml")

    families: dict[str, dict] = {}
    implementations: dict[tuple[str, str], dict] = {}
    cases: dict[str, dict] = {}

    for path in family_manifests:
        data = load_manifest(path)
        errors.extend(validate(data, schema_files["family"], str(path.relative_to(ROOT))))
        family_id = data.get("family_id")
        if isinstance(family_id, str):
            families[family_id] = data

    for path in implementation_manifests:
        data = load_manifest(path)
        errors.extend(validate(data, schema_files["implementation"], str(path.relative_to(ROOT))))
        family_id = data.get("family_id")
        implementation_id = data.get("implementation_id")
        if isinstance(family_id, str) and isinstance(implementation_id, str):
            implementations[(family_id, implementation_id)] = data

    for path in case_manifests:
        data = load_manifest(path)
        rel = str(path.relative_to(ROOT))
        errors.extend(validate(data, schema_files["case"], rel))
        project = data.get("project")
        case_id = data.get("case_id")
        family_id = data.get("family_id")
        implementation_id = data.get("implementation_id")
        if isinstance(project, str) and isinstance(case_id, str):
            full_case_id = f"{project}/{case_id}"
            cases[full_case_id] = data
            if family_id != project:
                errors.append(f"{rel}: family_id must match project for current layout")
        source_ref = data.get("source_ref")
        expected_ref = expected_source_ref(data)
        if not isinstance(source_ref, str) or not source_ref:
            errors.append(f"{rel}: source_ref must be a non-empty string")
        elif expected_ref is not None and source_ref != expected_ref:
            errors.append(f"{rel}: source_ref must match pinned upstream source {expected_ref!r}")
        if not isinstance(family_id, str) or family_id not in families:
            errors.append(f"{rel}: unknown family_id {family_id!r}")
        if not isinstance(family_id, str) or not isinstance(implementation_id, str):
            errors.append(f"{rel}: implementation reference is incomplete")
        elif (family_id, implementation_id) not in implementations:
            errors.append(f"{rel}: unknown implementation {(family_id, implementation_id)!r}")

    for path in task_manifests:
        data = load_manifest(path)
        rel = str(path.relative_to(ROOT))
        errors.extend(validate(data, schema_files["task"], rel))
        case_id = data.get("case_id")
        family_id = data.get("family_id")
        implementation_id = data.get("implementation_id")
        source_ref = data.get("source_ref")
        if not isinstance(case_id, str) or case_id not in cases:
            errors.append(f"{rel}: unknown case_id {case_id!r}")
        else:
            parent_case_id = f"{path.parent.parent.parent.name}/{path.parent.parent.name}"
            if case_id != parent_case_id:
                errors.append(
                    f"{rel}: case_id {case_id!r} does not match parent case {parent_case_id!r}"
                )
            else:
                case_record = cases[case_id]
                case_source_ref = case_record.get("source_ref")
                if source_ref != case_source_ref:
                    errors.append(
                        f"{rel}: source_ref {source_ref!r} does not match parent case source_ref {case_source_ref!r}"
                    )
        if not isinstance(family_id, str) or family_id not in families:
            errors.append(f"{rel}: unknown family_id {family_id!r}")
        if not isinstance(family_id, str) or not isinstance(implementation_id, str):
            errors.append(f"{rel}: implementation reference is incomplete")
        elif (family_id, implementation_id) not in implementations:
            errors.append(f"{rel}: unknown implementation {(family_id, implementation_id)!r}")
        interface_version = data.get("task_interface_version")
        if not isinstance(interface_version, int) or interface_version < 1:
            errors.append(f"{rel}: task_interface_version must be an integer >= 1")
        evaluation_engine = data.get("evaluation_engine")
        theorem_name = data.get("theorem_name")
        proof_family = data.get("proof_family")
        implementation_files = data.get("implementation_files")
        specification_files = data.get("specification_files")
        editable_files = data.get("editable_files")
        reference_solution_module = data.get("reference_solution_module")
        reference_solution_declaration = data.get("reference_solution_declaration")
        if not isinstance(source_ref, str) or not source_ref:
            errors.append(f"{rel}: source_ref must be a non-empty string")
        if evaluation_engine != "lean_proof_generation":
            errors.append(f"{rel}: evaluation_engine must be 'lean_proof_generation'")
        if not isinstance(theorem_name, str) or not theorem_name:
            errors.append(f"{rel}: theorem_name must be a non-empty string")
        if proof_family not in PROOF_FAMILIES:
            errors.append(f"{rel}: proof_family must be one of {sorted(PROOF_FAMILIES)}")
        if not isinstance(implementation_files, list) or not implementation_files:
            errors.append(f"{rel}: implementation_files must be a non-empty list")
        if not isinstance(specification_files, list) or not specification_files:
            errors.append(f"{rel}: specification_files must be a non-empty list")
        if not isinstance(editable_files, list) or len(editable_files) != 1:
            errors.append(f"{rel}: editable_files must contain exactly one editable Lean file")
        for field_name, paths in (
            ("implementation_files", implementation_files),
            ("specification_files", specification_files),
            ("editable_files", editable_files),
        ):
            if isinstance(paths, list):
                for candidate in paths:
                    candidate_path = ROOT / str(candidate)
                    if not candidate_path.exists():
                        errors.append(f"{rel}: {field_name} entry does not exist: {candidate}")
        if isinstance(editable_files, list):
            for editable in editable_files:
                editable_path = str(editable)
                if not editable_path.startswith("Benchmark/Generated/") or not editable_path.endswith(".lean"):
                    errors.append(
                        f"{rel}: editable_files entries must live under Benchmark/Generated/.../*.lean"
                    )
        if not isinstance(reference_solution_module, str) or not reference_solution_module:
            errors.append(f"{rel}: reference_solution_module must be a non-empty string")
        if not isinstance(reference_solution_declaration, str) or not reference_solution_declaration:
            errors.append(f"{rel}: reference_solution_declaration must be a non-empty string")
        elif theorem_name != reference_solution_declaration:
            errors.append(f"{rel}: theorem_name must match reference_solution_declaration")

    for family_id, data in families.items():
        for case_id in data.get("case_ids", []):
            if case_id not in cases:
                errors.append(f"families/{family_id}/family.yaml: missing case reference {case_id}")
        for implementation_id in data.get("implementation_ids", []):
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
