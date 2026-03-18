#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
RESULTS_DIR = ROOT / "results"
TASK_RESULTS_DIR = RESULTS_DIR / "tasks"

if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

from manifest_utils import load_manifest_data

RUNNABLE_STAGES = {"build_green", "proof_partial", "proof_complete"}
PROOF_READY_STATUSES = {"partial", "complete"}
SPEC_READY_STATUSES = {"draft", "frozen", "partial", "complete"}


def normalize_optional_string(value: object) -> str | None:
    if value is None:
        return None
    if isinstance(value, list):
        return None
    text = str(value).strip()
    return text or None


def normalize_list(value: object) -> list[str]:
    if value is None:
        return []
    if not isinstance(value, list):
        raise ValueError(f"expected list, got {type(value).__name__}")
    return [str(item).strip() for item in value]


def derive_spec_module(compile_target: str | None) -> str | None:
    if compile_target and compile_target.endswith(".Compile"):
        return compile_target[: -len(".Compile")] + ".Specs"
    return None


def task_ref_from_manifest(task_manifest: Path) -> str:
    case_dir = task_manifest.parent.parent
    return f"{case_dir.parent.name}/{case_dir.name}/{task_manifest.stem}"


def resolve_task_manifest(task_ref: str) -> Path:
    parts = task_ref.split("/")
    if len(parts) != 3:
        raise SystemExit("usage: <project/case_id/task_id>")

    project, case_name, task_id = parts
    candidates = [
        ROOT / "cases" / project / case_name / "tasks" / f"{task_id}.yaml",
        ROOT / "backlog" / project / case_name / "tasks" / f"{task_id}.yaml",
    ]
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    raise SystemExit(f"task manifest not found for {task_ref}")


def discover_task_refs(suite_filter: str = "active") -> list[str]:
    refs: list[str] = []
    if suite_filter == "all":
        roots = [ROOT / "cases", ROOT / "backlog"]
    elif suite_filter == "backlog":
        roots = [ROOT / "backlog"]
    else:
        roots = [ROOT / "cases"]

    for root in roots:
        if not root.exists():
            continue
        for task_manifest in sorted(root.glob("*/*/tasks/*.yaml")):
            refs.append(task_ref_from_manifest(task_manifest))
    return refs


def load_case_record(case_manifest: Path) -> dict[str, Any]:
    data = load_manifest_data(case_manifest)
    suite = "active" if case_manifest.parts[-4] == "cases" else "backlog"
    return {
        "case_id": f"{data['project']}/{data['case_id']}",
        "suite": suite,
        "stage": data["stage"],
        "lean_target": normalize_optional_string(data.get("lean_target")),
        "failure_reason": normalize_optional_string(data.get("failure_reason")),
        "translation_status": normalize_optional_string(data.get("translation_status")) or "not_started",
        "spec_status": normalize_optional_string(data.get("spec_status")) or "not_started",
        "proof_status": normalize_optional_string(data.get("proof_status")) or "not_started",
        "manifest_path": str(case_manifest.relative_to(ROOT)),
    }


def load_task_record(task_manifest: Path) -> dict[str, Any]:
    task_data = load_manifest_data(task_manifest)
    case_manifest = task_manifest.parent.parent / "case.yaml"
    case_data = load_case_record(case_manifest)

    task_id = normalize_optional_string(task_data.get("task_id")) or task_manifest.stem
    task_ref = f"{case_data['case_id']}/{task_id}"

    spec_module = normalize_optional_string(task_data.get("spec_target")) or derive_spec_module(
        case_data["lean_target"]
    )
    spec_decl = normalize_optional_string(task_data.get("statement_id"))

    proof_module = normalize_optional_string(task_data.get("proof_target"))
    proof_decl = normalize_optional_string(task_data.get("statement_id")) if proof_module else None

    translation_status = normalize_optional_string(task_data.get("translation_status")) or case_data["translation_status"]
    spec_status = normalize_optional_string(task_data.get("spec_status")) or case_data["spec_status"]
    proof_status = normalize_optional_string(task_data.get("proof_status")) or case_data["proof_status"]

    readiness = {
        "translation": "ready" if case_data["lean_target"] and translation_status == "translated" and case_data["stage"] in RUNNABLE_STAGES else "blocked",
        "spec": "ready" if spec_module and spec_decl and spec_status in SPEC_READY_STATUSES else "planned",
        "proof": "ready" if proof_module and proof_decl and proof_status in PROOF_READY_STATUSES else "planned",
    }

    return {
        "benchmark": "verity-benchmark",
        "schema_version": 1,
        "task_ref": task_ref,
        "task_id": task_id,
        "case_id": case_data["case_id"],
        "suite": case_data["suite"],
        "stage": case_data["stage"],
        "track": normalize_optional_string(task_data.get("track")) or "unspecified",
        "property_class": normalize_optional_string(task_data.get("property_class")) or "unspecified",
        "category": normalize_optional_string(task_data.get("category")) or "unspecified",
        "difficulty": normalize_optional_string(task_data.get("difficulty")) or "unspecified",
        "statement_id": normalize_optional_string(task_data.get("statement_id")),
        "allowed_files": normalize_list(task_data.get("allowed_files")),
        "translation_status": translation_status,
        "spec_status": spec_status,
        "proof_status": proof_status,
        "failure_reason": case_data["failure_reason"],
        "manifest_path": str(task_manifest.relative_to(ROOT)),
        "case_manifest_path": case_data["manifest_path"],
        "targets": {
            "compile_target": case_data["lean_target"],
            "spec_target_module": spec_module,
            "spec_target_decl": spec_decl,
            "proof_target_module": proof_module,
            "proof_target_decl": proof_decl,
        },
        "readiness": readiness,
    }


def run_command(command: list[str]) -> tuple[int, str]:
    completed = subprocess.run(
        command,
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    output = (completed.stdout + completed.stderr).strip()
    return completed.returncode, output
def select_primary_target(task: dict[str, Any]) -> tuple[str | None, str | None, str | None]:
    targets = task["targets"]
    readiness = task["readiness"]
    if readiness["proof"] == "ready":
        return "proof", targets["proof_target_module"], targets["proof_target_decl"]
    if readiness["spec"] == "ready":
        return "spec", targets["spec_target_module"], targets["spec_target_decl"]
    if readiness["translation"] == "ready":
        return "translation", targets["compile_target"], None
    return None, None, None


def execute_task(task_ref: str) -> tuple[int, Path]:
    task_manifest = resolve_task_manifest(task_ref)
    task = load_task_record(task_manifest)
    TASK_RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    result_path = TASK_RESULTS_DIR / f"{task_ref.replace('/', '__')}.json"

    selected_kind, selected_target, selected_decl = select_primary_target(task)
    started_at = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    start = time.time()
    failure_mode: str | None = None
    execution_status = "not_runnable"
    execution_output = ""
    command: list[str] = []

    if task["stage"] not in RUNNABLE_STAGES:
        failure_mode = task["failure_reason"] or "stage_blocked"
    elif selected_kind == "proof":
        command = ["lake", "build", selected_target]
        code, execution_output = run_command(command)
        execution_status = "passed" if code == 0 else "failed"
        if code != 0:
            failure_mode = "proof_target_check_failed"
    elif selected_kind == "spec":
        command = ["lake", "build", selected_target]
        code, execution_output = run_command(command)
        execution_status = "passed" if code == 0 else "failed"
        if code != 0:
            failure_mode = "spec_target_check_failed"
    elif selected_kind == "translation":
        command = ["lake", "build", selected_target]
        code, execution_output = run_command(command)
        execution_status = "passed" if code == 0 else "failed"
        if code != 0:
            failure_mode = "translation_target_failed"
    else:
        failure_mode = task["failure_reason"] or "no_executable_target"

    completed_at = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    duration_seconds = round(time.time() - start, 3)

    payload = {
        "benchmark": task["benchmark"],
        "schema_version": task["schema_version"],
        "unit": "task",
        "run_id": f"{task_ref}:{started_at}",
        "task_ref": task["task_ref"],
        "task_id": task["task_id"],
        "case_id": task["case_id"],
        "suite": task["suite"],
        "track": task["track"],
        "property_class": task["property_class"],
        "category": task["category"],
        "difficulty": task["difficulty"],
        "statement_id": task["statement_id"],
        "command": command,
        "started_at": started_at,
        "completed_at": completed_at,
        "outcome": execution_status,
        "exit_code": 1 if execution_status == "failed" else 0,
        "status": execution_status,
        "failure_mode": failure_mode,
        "failure_reason": task["failure_reason"],
        "manifests": {
            "task": task["manifest_path"],
            "case": task["case_manifest_path"],
        },
        "artifacts": [str(result_path.relative_to(ROOT))],
        "metrics": {
            "duration_seconds": duration_seconds,
        },
        "environment": {
            "stage": task["stage"],
            "translation_status": task["translation_status"],
            "spec_status": task["spec_status"],
            "proof_status": task["proof_status"],
            "selected_target_kind": selected_kind,
            "selected_target": selected_target,
            "selected_declaration": selected_decl,
        },
        "allowed_files": task["allowed_files"],
        "readiness": task["readiness"],
        "targets": task["targets"],
        "output": execution_output,
    }
    result_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return (1 if execution_status == "failed" else 0), result_path


def aggregate_results(task_refs: list[str]) -> dict[str, Any]:
    results = []
    for task_ref in task_refs:
        path = TASK_RESULTS_DIR / f"{task_ref.replace('/', '__')}.json"
        if path.exists():
            results.append(json.loads(path.read_text(encoding="utf-8")))

    status_counts = Counter(item["status"] for item in results)
    failure_mode_counts = Counter(item["failure_mode"] for item in results if item["failure_mode"])
    by_track: dict[str, Counter[str]] = defaultdict(Counter)
    by_property_class: dict[str, Counter[str]] = defaultdict(Counter)
    by_case: dict[str, list[dict[str, Any]]] = defaultdict(list)
    readiness_counts: dict[str, dict[str, int]] = {}

    for item in results:
        by_track[item["track"]][item["status"]] += 1
        by_property_class[item["property_class"]][item["status"]] += 1
        by_case[item["case_id"]].append(item)

    for key in ("translation", "spec", "proof"):
        readiness_counts[key] = dict(
            sorted(Counter(item["readiness"][key] for item in results).items())
        )

    case_rows = []
    for case_id, case_results in sorted(by_case.items()):
        statuses = [entry["status"] for entry in case_results]
        if any(status == "failed" for status in statuses):
            case_status = "failed"
        elif any(status == "passed" for status in statuses):
            case_status = "passed"
        else:
            case_status = "not_runnable"
        case_rows.append(
            {
                "case_id": case_id,
                "status": case_status,
                "task_count": len(case_results),
                "status_counts": dict(sorted(Counter(statuses).items())),
            }
        )

    task_summary = {
        "benchmark": "verity-benchmark",
        "schema_version": 1,
        "unit": "task",
        "total_tasks": len(results),
        "status_counts": dict(sorted(status_counts.items())),
        "failure_mode_counts": dict(sorted(failure_mode_counts.items())),
        "track_status_counts": {
            key: dict(sorted(value.items()))
            for key, value in sorted(by_track.items())
        },
        "property_class_status_counts": {
            key: dict(sorted(value.items()))
            for key, value in sorted(by_property_class.items())
        },
        "readiness_counts": readiness_counts,
        "tasks": [item["task_ref"] for item in results],
    }
    case_summary = {
        "benchmark": "verity-benchmark",
        "schema_version": 1,
        "unit": "case-secondary",
        "total_cases": len(case_rows),
        "status_counts": dict(sorted(Counter(item["status"] for item in case_rows).items())),
        "cases": case_rows,
    }
    return {"task_summary": task_summary, "case_summary": case_summary}


def main() -> int:
    parser = argparse.ArgumentParser(description="Task-oriented benchmark runner")
    subparsers = parser.add_subparsers(dest="command", required=True)

    list_parser = subparsers.add_parser("list", help="List task refs")
    list_parser.add_argument("--suite", choices=["active", "backlog", "all"], default="active")

    run_parser = subparsers.add_parser("run", help="Run one task")
    run_parser.add_argument("task_ref")

    aggregate_parser = subparsers.add_parser("aggregate", help="Aggregate existing task results")
    aggregate_parser.add_argument("task_refs", nargs="+")

    args = parser.parse_args()

    if args.command == "list":
        for task_ref in discover_task_refs(args.suite):
            print(task_ref)
        return 0

    if args.command == "run":
        code, result_path = execute_task(args.task_ref)
        print(result_path.relative_to(ROOT))
        return code

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    aggregated = aggregate_results(args.task_refs)
    (RESULTS_DIR / "summary.json").write_text(
        json.dumps(aggregated["task_summary"], indent=2) + "\n",
        encoding="utf-8",
    )
    (RESULTS_DIR / "case_summary.json").write_text(
        json.dumps(aggregated["case_summary"], indent=2) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
