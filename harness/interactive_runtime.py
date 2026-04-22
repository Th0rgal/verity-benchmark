from __future__ import annotations

import json
import os
import re
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from task_runner import ROOT, run_command as lean_run_command


PLACEHOLDER_PATTERN = re.compile(r"\b(sorry|admit|axiom)\b")
# Match standalone `?_` holes only (not `?x` metavariables used in valid tactics).
HOLE_PATTERN = re.compile(r"(?<!\w)\?_(?!\w)")
DEF_PATTERN = re.compile(r"^\s*(?:def|theorem|lemma|abbrev|opaque)\s+([A-Za-z0-9_'.]+)")
HIDDEN_PROOF_IMPORT_PATTERN = re.compile(
    r"^\s*(?:import|open|export)\s+Benchmark\.Cases\..*\.Proofs\b", re.MULTILINE
)
IMPORT_PATTERN = re.compile(r"^\s*import\s+([A-Za-z0-9_.']+)\s*$", re.MULTILINE)


@dataclass(frozen=True)
class RuntimePaths:
    editable_rel_path: str
    theorem_name: str
    implementation_files: tuple[str, ...]
    specification_files: tuple[str, ...]
    public_files: tuple[str, ...]


class TaskProofRuntime:
    def __init__(self, task: dict[str, Any]) -> None:
        editable_files = [str(item) for item in task["editable_files"]]
        if len(editable_files) != 1:
            raise ValueError("tasks must declare exactly one editable Lean file")
        editable_rel_path = editable_files[0]
        self._check_history: list[str] = []  # failure_class history for stagnation detection
        self._task = task  # store for hint escalation
        self._best_error_count: int | None = None
        self._best_first_error_line: int | None = None
        # Fingerprints of hint texts already surfaced this session. Used to
        # avoid echoing the same repair advice verbatim across consecutive
        # failures — repeated identical hints are pure noise and train the
        # model to ignore the list instead of acting on it.
        self._emitted_hint_keys: set[str] = set()
        # Normalised fingerprint of the previous failing Lean details text,
        # plus a count of how many times the same fingerprint has repeated
        # in a row. Used to detect "no-progress loops" where the model
        # resubmits a proof that yields byte-identical errors — corpus
        # analysis found 12/29 failing tasks hit this pattern.
        self._last_details_fp: str | None = None
        self._same_details_streak: int = 0
        self.paths = RuntimePaths(
            editable_rel_path=editable_rel_path,
            theorem_name=str(task["theorem_name"]),
            implementation_files=tuple(str(item) for item in task["implementation_files"]),
            specification_files=tuple(str(item) for item in task["specification_files"]),
            public_files=tuple(
                str(item)
                for item in [
                    *task["implementation_files"],
                    *task["specification_files"],
                    *editable_files,
                ]
            ),
        )
        self.current_proof_text = self._read_repo_file(editable_rel_path)
        self.expected_theorem_signature = self._extract_theorem_signature(self.current_proof_text)
        self.allowed_task_modules = frozenset(self._module_name(path) for path in self.paths.public_files)

    def _read_repo_file(self, rel_path: str) -> str:
        path = ROOT / rel_path
        if not path.is_file():
            raise FileNotFoundError(rel_path)
        return path.read_text(encoding="utf-8")

    def read_public_file(self, rel_path: str) -> dict[str, Any]:
        if rel_path not in self.paths.public_files:
            return {
                "status": "rejected",
                "reason": "path_not_public_for_task",
                "allowed_files": list(self.paths.public_files),
            }
        if rel_path == self.paths.editable_rel_path:
            return {"status": "ok", "path": rel_path, "content": self.current_proof_text}
        try:
            return {"status": "ok", "path": rel_path, "content": self._read_repo_file(rel_path)}
        except FileNotFoundError:
            return {"status": "missing", "path": rel_path}

    def write_editable_proof(self, content: str, *, check: bool = True) -> dict[str, Any]:
        self.current_proof_text = content if content.endswith("\n") else f"{content}\n"
        warnings: list[dict[str, str]] = []
        if not self.current_proof_text.strip():
            warnings.append({"kind": "empty_content", "detail": "candidate is empty"})
        if PLACEHOLDER_PATTERN.search(self.current_proof_text):
            warnings.append({
                "kind": "placeholder_detected",
                "detail": "contains `sorry`/`admit`/`axiom`; replace before run_lean_check.",
            })
        if HIDDEN_PROOF_IMPORT_PATTERN.search(self.current_proof_text):
            warnings.append({
                "kind": "hidden_proof_import_detected",
                "detail": "remove Benchmark.Cases.*.Proofs import/open/export.",
            })
        blocked = self._find_blocked_case_imports(self.current_proof_text)
        if blocked:
            warnings.append({
                "kind": "hidden_case_import_detected",
                "detail": "non-public imports: " + ", ".join(blocked),
            })
        if HOLE_PATTERN.search(self.current_proof_text):
            warnings.append({
                "kind": "unfilled_hole",
                "detail": "proof still contains `?_` holes; fill before submitting.",
            })
        candidate_signature = self._extract_theorem_signature(self.current_proof_text)
        if candidate_signature != self.expected_theorem_signature:
            warnings.append({
                "kind": "theorem_statement_mismatch",
                "detail": "editable theorem signature changed; revert to the original statement.",
            })
        result: dict[str, Any] = {
            "status": "ok_with_warnings" if warnings else "ok",
            "path": self.paths.editable_rel_path,
            "bytes": len(self.current_proof_text.encode("utf-8")),
            "lines": len(self.current_proof_text.splitlines()),
        }
        if warnings:
            result["warnings"] = warnings
        # Fold the Lean check into the write. Each write+check used to cost
        # two tool slots and two model round-trips; inlining saves one full
        # round-trip (hundreds of ms to seconds of LLM latency per proof
        # iteration) and doubles the effective budget for proof exploration.
        # The caller can disable by passing check=False (kept for callers
        # that only want to stage a draft without paying for Lean).
        if check:
            # Reuse the full run_lean_check pipeline (auto-heal + annotation +
            # repair hints) so downstream success/failure detection is
            # identical to a bare run_lean_check call. Write-time metadata
            # (path, bytes, lines, warnings) stays visible in the result so
            # the model still sees format warnings like non_public_imports
            # alongside the Lean verdict.
            result.update(self.execute_tool("run_lean_check", {}))
        return result

    def search_public_defs(self, query: str, *, limit: int = 20) -> dict[str, Any]:
        query_text = query.strip()
        if not query_text:
            return {"status": "rejected", "reason": "query_must_not_be_empty"}
        lowered = query_text.lower()
        matches: list[dict[str, Any]] = []
        for rel_path in self.paths.implementation_files + self.paths.specification_files:
            path = ROOT / rel_path
            if not path.is_file():
                continue
            for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
                name_match = DEF_PATTERN.match(line)
                if not name_match:
                    continue
                def_name = name_match.group(1)
                if lowered not in def_name.lower() and lowered not in line.lower():
                    continue
                matches.append(
                    {
                        "path": rel_path,
                        "line": line_no,
                        "name": def_name,
                        "declaration": line.strip(),
                    }
                )
                if len(matches) >= limit:
                    return {"status": "ok", "query": query_text, "matches": matches, "truncated": True}
        return {"status": "ok", "query": query_text, "matches": matches, "truncated": False}

    def inspect_goals(self) -> dict[str, Any]:
        holes = sorted(set(HOLE_PATTERN.findall(self.current_proof_text)))
        if not holes:
            return {
                "status": "unsupported",
                "reason": "goal_inspection_requires_explicit_hole",
                "details": "Write the proof with a `?_` or named hole first, then retry goal inspection.",
            }
        evaluation = self.evaluate_current(check_goals=True)
        return {
            "status": "ok" if evaluation["status"] == "failed" else "passed",
            "holes": holes,
            "details": evaluation["details"],
            "command": evaluation.get("command"),
        }

    def try_tactic_at_hole(self, tactic: str) -> dict[str, Any]:
        """Try replacing all ?_ holes with a specific tactic and check if it works.

        This is a lightweight alternative to PyPantograph for targeted tactic execution.
        The original proof is preserved if the tactic fails.
        """
        if not tactic.strip():
            return {"status": "rejected", "reason": "tactic_must_not_be_empty"}
        original = self.current_proof_text
        # Replace standalone `?_` holes (not named holes like `?_foo` and not
        # identifiers ending in `?_`). Must match HOLE_PATTERN so both tools
        # agree on what counts as a hole.
        modified = HOLE_PATTERN.sub(tactic.strip(), original)
        if modified == original:
            return {
                "status": "unsupported",
                "reason": "no_holes_found",
                "details": "No `?_` holes in the current proof. Write a proof with `?_` holes first.",
            }
        evaluation = self.evaluate_candidate(modified)
        if evaluation.get("status") == "passed":
            self.current_proof_text = modified
            return {
                "status": "passed",
                "tactic": tactic.strip(),
                "details": "Tactic succeeded. Proof updated.",
            }
        return {
            "status": "failed",
            "tactic": tactic.strip(),
            "details": evaluation.get("details", "")[:2000],
            "failure_class": classify_failure(str(evaluation.get("details", ""))),
        }

    def evaluate_current(self, *, check_goals: bool = False) -> dict[str, Any]:
        return self.evaluate_candidate(self.current_proof_text, check_goals=check_goals)

    def preflight_candidate(self, candidate_text: str) -> dict[str, Any] | None:
        """Fast local checks that don't require running Lean. Returns a failure dict or None if OK."""
        if not candidate_text.strip():
            return {
                "status": "failed",
                "failure_mode": "empty_response",
                "details": "agent response was empty",
            }

        if PLACEHOLDER_PATTERN.search(candidate_text):
            return {
                "status": "failed",
                "failure_mode": "placeholder_detected",
                "details": "candidate proof contains a rejected placeholder token",
            }

        if HIDDEN_PROOF_IMPORT_PATTERN.search(candidate_text):
            return {
                "status": "failed",
                "failure_mode": "hidden_proof_import_detected",
                "details": "candidate proof imports hidden Benchmark.Cases.*.Proofs modules",
            }

        blocked_imports = self._find_blocked_case_imports(candidate_text)
        if blocked_imports:
            return {
                "status": "failed",
                "failure_mode": "hidden_case_import_detected",
                "details": (
                    "candidate proof imports non-public Benchmark.Cases modules: "
                    + ", ".join(blocked_imports)
                ),
            }

        candidate_signature = self._extract_theorem_signature(candidate_text)
        if candidate_signature != self.expected_theorem_signature:
            return {
                "status": "failed",
                "failure_mode": "theorem_statement_mismatch",
                "details": "candidate proof changed the editable theorem statement",
            }

        return None

    def evaluate_candidate(self, candidate_text: str, *, check_goals: bool = False) -> dict[str, Any]:
        preflight_failure = self.preflight_candidate(candidate_text)
        if preflight_failure is not None:
            return preflight_failure

        with tempfile.TemporaryDirectory(prefix="verity-benchmark-agent-") as tmp_dir:
            workspace = Path(tmp_dir) / "workspace"
            self._materialize_workspace(workspace)
            editable_path = workspace / self.paths.editable_rel_path
            editable_path.parent.mkdir(parents=True, exist_ok=True)
            editable_path.write_text(candidate_text, encoding="utf-8")

            if check_goals:
                check_path = editable_path
                command = ["lake", "env", "lean", "--root=.", str(check_path.relative_to(workspace))]
            else:
                check_path = workspace / "CandidateCheck.lean"
                check_path.write_text(
                    candidate_text.rstrip() + f"\n\n#check {self.paths.theorem_name}\n",
                    encoding="utf-8",
                )
                command = ["lake", "env", "lean", "--root=.", str(check_path.relative_to(workspace))]
            code, output = lean_run_command(command, cwd=workspace)
            if code != 0:
                return {
                    "status": "failed",
                    "failure_mode": "lean_check_failed",
                    "details": output,
                    "command": command,
                    "candidate_workspace": str(editable_path.relative_to(workspace)),
                }
            return {
                "status": "passed",
                "failure_mode": None,
                "details": output,
                "command": command,
                "candidate_workspace": str(editable_path.relative_to(workspace)),
            }

    def tool_specs(self) -> list[dict[str, Any]]:
        return [
            {
                "type": "function",
                "function": {
                    "name": "read_public_file",
                    "description": "Read one task-scoped public Lean file from implementation_files, specification_files, or the editable proof.",
                    "parameters": {
                        "type": "object",
                        "additionalProperties": False,
                        "required": ["path"],
                        "properties": {
                            "path": {
                                "type": "string",
                                "enum": list(self.paths.public_files),
                            }
                        },
                    },
                },
            },
            {
                "type": "function",
                "function": {
                    "name": "write_editable_proof",
                    "description": "Replace the entire editable proof file with complete Lean code and automatically run the Lean check. The response reports status (passed/failed/ok/ok_with_warnings) and, on failure, failure_mode, details, and failure_class. A separate run_lean_check call is not needed after this.",
                    "parameters": {
                        "type": "object",
                        "additionalProperties": False,
                        "required": ["content"],
                        "properties": {
                            "content": {
                                "type": "string",
                            }
                        },
                    },
                },
            },
            {
                "type": "function",
                "function": {
                    "name": "run_lean_check",
                    "description": "Run the official harness Lean check for the current editable proof.",
                    "parameters": {
                        "type": "object",
                        "additionalProperties": False,
                        "properties": {},
                    },
                },
            },
            {
                "type": "function",
                "function": {
                    "name": "inspect_lean_goals",
                    "description": "Inspect current Lean diagnostics for explicit proof holes in the editable file. Returns unsupported if no hole is present.",
                    "parameters": {
                        "type": "object",
                        "additionalProperties": False,
                        "properties": {},
                    },
                },
            },
            {
                "type": "function",
                "function": {
                    "name": "search_public_defs",
                    "description": "Search public implementation/specification files for matching def/theorem/lemma names.",
                    "parameters": {
                        "type": "object",
                        "additionalProperties": False,
                        "required": ["query"],
                        "properties": {
                            "query": {"type": "string"},
                            "limit": {"type": "integer", "minimum": 1, "maximum": 50},
                        },
                    },
                },
            },
            {
                "type": "function",
                "function": {
                    "name": "try_tactic_at_hole",
                    "description": "Try replacing all `?_` holes in the current proof with a specific tactic and check if it compiles. Preserves the original proof if it fails. Useful for testing tactics like `simp_all [...]`, `omega`, `decide`, or `duper [...]`.",
                    "parameters": {
                        "type": "object",
                        "additionalProperties": False,
                        "required": ["tactic"],
                        "properties": {
                            "tactic": {
                                "type": "string",
                                "description": "The Lean tactic to try at each ?_ hole.",
                            }
                        },
                    },
                },
            },
        ]

    def execute_tool(self, name: str, arguments: dict[str, Any]) -> dict[str, Any]:
        if name == "read_public_file":
            return self.read_public_file(str(arguments.get("path", "")))
        if name == "write_editable_proof":
            return self.write_editable_proof(str(arguments.get("content", "")))
        if name == "run_lean_check":
            result = self.evaluate_current()
            # Auto-heal environment errors (missing .olean) once before annotating.
            if result.get("status") == "failed" and result.get("failure_mode") == "lean_check_failed":
                details = str(result.get("details", ""))
                if classify_failure(details) == "environment_error":
                    module_name = _missing_olean_module(details)
                    healed = _attempt_lake_build(module_name)
                    if healed:
                        result = self.evaluate_current()
            if result.get("status") == "failed":
                result = self._annotate_check_result(result)
                # Also add structured repair hints from main's guidance
                if result.get("failure_mode") == "lean_check_failed":
                    guidance = _build_repair_guidance(str(result.get("details", "")))
                    if guidance:
                        existing = result.get("repair_hints", [])
                        if isinstance(existing, list):
                            existing.append(guidance)
                            result["repair_hints"] = existing
                        else:
                            result["repair_hints"] = [existing, guidance] if existing else [guidance]
            return result
        if name == "inspect_lean_goals":
            return self.inspect_goals()
        if name == "search_public_defs":
            limit = int(arguments.get("limit", 20))
            return self.search_public_defs(str(arguments.get("query", "")), limit=limit)
        if name == "try_tactic_at_hole":
            return self.try_tactic_at_hole(str(arguments.get("tactic", "")))
        return {"status": "rejected", "reason": "unknown_tool", "tool": name}

    def _annotate_check_result(self, result: dict[str, Any]) -> dict[str, Any]:
        """Annotate a failed check result with failure classification and repair hints."""
        failure_mode = result.get("failure_mode", "")
        # Only track actual Lean checker failures for stagnation detection,
        # not preflight failures (empty_response, placeholder_detected, etc.)
        is_lean_failure = failure_mode == "lean_check_failed"
        details = str(result.get("details", ""))
        # Preflight failures carry English-language details that classify_failure
        # can't pattern-match, so they all collapse to "other" and the model gets
        # no targeted hint. Map the failure_mode directly to a class name so the
        # model sees e.g. "placeholder_detected" instead of "other" and
        # _build_check_hints can dispatch a specific hint.
        if not is_lean_failure and failure_mode in _PREFLIGHT_FAILURE_MODES:
            failure_class = failure_mode
        else:
            failure_class = classify_failure(details)
        hints = _build_check_hints(failure_class, details)
        annotated = dict(result)
        annotated["failure_class"] = failure_class

        # environment_error is infrastructure, not a proof problem. Don't track
        # stagnation for it (retrying won't help) and tag the result clearly.
        if failure_class == "environment_error":
            annotated["environment_error"] = True
            if hints:
                annotated["repair_hints"] = hints
            return annotated

        if not is_lean_failure:
            if hints:
                annotated["repair_hints"] = hints
            return annotated

        # Track failure history for stagnation detection (Lean check failures only)
        self._check_history.append(failure_class)
        total_failures = len(self._check_history)

        # Count consecutive same-class failures
        same_class_count = 0
        for fc in reversed(self._check_history):
            if fc == failure_class:
                same_class_count += 1
            else:
                break

        # Detect true no-progress loops: the normalized error text matches the
        # previous failure byte-for-byte. This is a much stronger signal than
        # same-class stagnation — it proves the last edit had zero effect on
        # what Lean actually saw.
        details_fp = _normalize_details_fp(details)
        if details_fp and details_fp == self._last_details_fp:
            self._same_details_streak += 1
        else:
            self._same_details_streak = 1
        self._last_details_fp = details_fp

        # Escalate on either: 2+ consecutive same-class failures, or 4+ total failures
        if same_class_count >= 2 or total_failures >= 4:
            if same_class_count >= 2:
                annotated["stagnation_warning"] = (
                    f"Same failure class '{failure_class}' repeated {same_class_count} times. "
                    "Your current approach is not working. Try a fundamentally different proof structure."
                )
            else:
                annotated["stagnation_warning"] = (
                    f"You have failed {total_failures} times across different error classes. "
                    "Step back and reconsider your proof strategy from scratch."
                )
            escalation = self._build_escalation_hint(failure_class)
            if escalation:
                hints.append(escalation)

        # When the error text is byte-identical to the previous attempt, the
        # model's latest edit had zero effect — hints must call this out
        # explicitly, not just repeat class-level advice. Keep this BEFORE
        # the dedup so the fingerprint-unique streak count is surfaced fresh
        # each time.
        if self._same_details_streak >= 2:
            hints.insert(0, (
                f"NO-PROGRESS LOOP DETECTED: your last {self._same_details_streak} "
                "submissions produced byte-identical Lean errors. The changes you are "
                "making do not reach the failing goal. Stop editing around the symptom. "
                "Instead: (1) `write_editable_proof` with the failing tactic replaced by "
                "`?_`, (2) `inspect_lean_goals` to read the real goal at that hole, "
                "(3) `try_tactic_at_hole` with tactics you have NOT tried yet "
                "(e.g. `simp_all`, `aesop`, `decide`, `exact?`, `constructor; all_goals ...`)."
            ))

        # Dedupe hints we've already shown this session. Repeated-verbatim hints
        # are noise: corpus analysis of failing tasks showed the same 4-5 hints
        # echoed across 5+ stagnation events, training the model to skip the
        # repair_hints list entirely. Only surface *new* advice each time.
        hints = self._filter_seen_hints(hints)
        if not hints and same_class_count >= 3:
            # All the standing advice has already been seen and isn't working.
            # Issue a one-shot pivot directive rather than sending an empty list,
            # which the model interprets as "nothing new, carry on".
            hints = [
                f"All prior repair hints for '{failure_class}' have now been repeated "
                f"{same_class_count} times without progress. Stop retrying variations of "
                f"the same proof. Next move: write a minimal skeleton with a `?_` hole at "
                f"the first failing step, call `inspect_lean_goals` to read the actual "
                f"goal state, then use `try_tactic_at_hole` to probe tactics one at a time."
            ]

        if hints:
            annotated["repair_hints"] = hints

        # Add structured error summary with progress tracking
        error_lines: list[int] = []
        for match in re.finditer(r":(\d+):\d+: error:", details):
            error_lines.append(int(match.group(1)))
        if error_lines:
            error_count = len(error_lines)
            first_error = min(error_lines)
            annotated["error_count"] = error_count
            annotated["first_error_line"] = first_error

            # Track progress relative to best seen
            progress_parts: list[str] = []
            if self._best_error_count is not None:
                if error_count < self._best_error_count:
                    progress_parts.append(f"errors reduced ({self._best_error_count} -> {error_count})")
                elif error_count > self._best_error_count:
                    progress_parts.append(f"errors increased ({self._best_error_count} -> {error_count}), reverting direction")
            if self._best_first_error_line is not None:
                if first_error > self._best_first_error_line:
                    progress_parts.append(f"first error moved deeper (line {self._best_first_error_line} -> {first_error})")
                elif first_error < self._best_first_error_line:
                    progress_parts.append(f"first error moved earlier (line {self._best_first_error_line} -> {first_error})")

            if progress_parts:
                annotated["progress"] = "; ".join(progress_parts)

            # Update best-seen metrics
            if self._best_error_count is None or error_count < self._best_error_count:
                self._best_error_count = error_count
            if self._best_first_error_line is None or first_error > self._best_first_error_line:
                self._best_first_error_line = first_error

        return annotated

    def _filter_seen_hints(self, hints: list[str]) -> list[str]:
        """Drop hints whose fingerprint has already been surfaced this session.

        Fingerprint = lowercased first 80 non-whitespace chars. Short enough
        that wording tweaks still dedupe, long enough to distinguish genuinely
        different hints.
        """
        fresh: list[str] = []
        for hint in hints:
            key = "".join(hint.lower().split())[:80]
            if key in self._emitted_hint_keys:
                continue
            self._emitted_hint_keys.add(key)
            fresh.append(hint)
        return fresh

    def _build_escalation_hint(self, failure_class: str) -> str | None:
        """Build an escalation hint when the model is stagnating on a failure class."""
        terms = extract_contract_simp_terms(self._task)
        if terms:
            full_set = ", ".join(terms)
            full_set += ", getStorage, setStorage, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd"
        else:
            full_set = ""

        if failure_class in ("simp_no_progress", "unsolved_goals", "rfl_failed", "unfold_failed"):
            if full_set:
                return (
                    f"ESCALATION: You are stuck. Do NOT use `unfold` on contract functions. "
                    f"Instead, pass them to `simp`. Here is the proof template:\n"
                    f"1. Start with `unfold <spec_name>` to unfold the spec definition only\n"
                    f"2. Use `by_cases` on each conditional branch BEFORE calling simp\n"
                    f"3. In EVERY branch, use: simp [{full_set}, <all hypotheses including by_cases vars>]\n"
                    f"4. For nested conditionals, nest `by_cases` inside the outer branch\n"
                    f"5. Never use bare `simp [h]` or `unfold ContractName.functionName`"
                )
        if failure_class == "unknown_identifier":
            return (
                "ESCALATION: Stop guessing identifier names. Use the search_public_defs tool "
                "to find the exact names from the implementation and specification files."
            )
        if failure_class == "type_mismatch":
            if full_set:
                return (
                    f"ESCALATION: Type mismatch usually means you're not simplifying enough. "
                    f"Use simp [{full_set}, <all hypotheses>] to fully reduce the expression."
                )
        return None

    def _materialize_workspace(self, workspace: Path) -> None:
        workspace.mkdir(parents=True, exist_ok=True)
        for rel_path in (
            "lakefile.lean",
            "lake-manifest.json",
            "lean-toolchain",
            ".lake",
        ):
            source = ROOT / rel_path
            target = workspace / rel_path
            if not source.exists():
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            os.symlink(source, target, target_is_directory=source.is_dir())
        for rel_path in self.paths.public_files:
            source = ROOT / rel_path
            target = workspace / rel_path
            target.parent.mkdir(parents=True, exist_ok=True)
            if rel_path == self.paths.editable_rel_path:
                target.write_text(self.current_proof_text, encoding="utf-8")
                continue
            if not source.is_file():
                continue
            os.symlink(source, target)

    def _extract_theorem_signature(self, text: str) -> str | None:
        short_name = self.paths.theorem_name.rsplit(".", 1)[-1]
        pattern = re.compile(
            rf"theorem\s+{re.escape(short_name)}\b(?P<signature>.*?)(?::=)",
            re.DOTALL,
        )
        match = pattern.search(text)
        if not match:
            return None
        signature = re.sub(r"/-.*?-/", " ", match.group("signature"), flags=re.DOTALL)
        signature = re.sub(r"--.*$", " ", signature, flags=re.MULTILINE)
        return " ".join(signature.split())

    def _find_blocked_case_imports(self, text: str) -> list[str]:
        blocked: list[str] = []
        for module_name in IMPORT_PATTERN.findall(text):
            if not module_name.startswith("Benchmark.Cases."):
                continue
            if module_name in self.allowed_task_modules:
                continue
            blocked.append(module_name)
        return sorted(set(blocked))

    @staticmethod
    def _module_name(rel_path: str) -> str:
        path = Path(rel_path)
        suffix = "".join(path.suffixes)
        module_path = str(path)
        if suffix:
            module_path = module_path[: -len(suffix)]
        return module_path.replace("/", ".")


_LAKE_BUILD_CACHE: dict[str, bool] = {}


def _attempt_lake_build(module_name: str | None) -> bool:
    """Best-effort `lake build` for a module. Returns True on success.

    Always invokes `lake build` — this is the self-heal path, called when the
    runtime observed a missing .olean at check time, so the previously cached
    "success" entry is stale and cannot be trusted. The cache is refreshed
    with the latest result so subsequent prebuild calls can short-circuit
    correctly.
    """
    if not module_name:
        return False
    if not module_name.startswith("Benchmark."):
        return False
    code, _output = lean_run_command(["lake", "build", module_name], cwd=ROOT)
    success = code == 0
    _LAKE_BUILD_CACHE[module_name] = success
    return success


def prebuild_task_modules(task: dict[str, Any]) -> list[dict[str, Any]]:
    """Pre-build implementation/specification .olean files for a task.

    Returns a list of build reports. Meant to be called once before starting
    the agent loop so on-the-fly compilation inside `lake env lean` does not
    race with fast agent retries.
    """
    reports: list[dict[str, Any]] = []
    targets: list[str] = []
    for rel_path in list(task.get("implementation_files", [])) + list(task.get("specification_files", [])):
        path = Path(rel_path)
        if path.suffix != ".lean":
            continue
        module_name = ".".join(path.with_suffix("").parts)
        # Only modules inside the `Benchmark` lean_lib are buildable via `lake build`.
        # Source-of-truth files under `cases/` are mirrored into `Benchmark/Cases/` and
        # that mirror is what lake actually compiles.
        if not module_name.startswith("Benchmark."):
            continue
        if module_name in targets:
            continue
        targets.append(module_name)
    for module_name in targets:
        if _LAKE_BUILD_CACHE.get(module_name):
            reports.append({"module": module_name, "status": "cached"})
            continue
        code, output = lean_run_command(["lake", "build", module_name], cwd=ROOT)
        success = code == 0
        if success:
            _LAKE_BUILD_CACHE[module_name] = True
        reports.append(
            {
                "module": module_name,
                "status": "ok" if success else "failed",
                "output": output[-600:] if not success else "",
            }
        )
    return reports


def extract_contract_simp_terms(task: dict[str, Any]) -> list[str]:
    """Extract concrete simp terms from implementation and specification files.

    Parses verity_contract storage field declarations, function names,
    and non-spec helper definitions to generate the simp lemma set.
    """
    terms: list[str] = []
    contract_name = ""
    for rel_path in task.get("implementation_files", []):
        path = ROOT / rel_path
        if not path.is_file():
            continue
        content = path.read_text(encoding="utf-8")
        contract_match = re.search(r"verity_contract\s+(\w+)\s+where", content)
        if contract_match:
            contract_name = contract_match.group(1)
        for field_match in re.finditer(
            r"^\s+(\w+)\s*:.*:=\s*slot\s+\d+", content, re.MULTILINE
        ):
            field_name = field_match.group(1)
            if contract_name:
                terms.append(f"{contract_name}.{field_name}")
        for fn_match in re.finditer(
            r"^\s+function\s+(\w+)\s*\(", content, re.MULTILINE
        ):
            fn_name = fn_match.group(1)
            if contract_name:
                terms.append(f"{contract_name}.{fn_name}")
    for rel_path in task.get("specification_files", []):
        path = ROOT / rel_path
        if not path.is_file():
            continue
        content = path.read_text(encoding="utf-8")
        for def_match in re.finditer(r"^def\s+(\w+)\b", content, re.MULTILINE):
            def_name = def_match.group(1)
            if not def_name.endswith("_spec") and def_name not in terms:
                terms.append(def_name)
    return terms


_FP_LINE_COL_RE = re.compile(r"CandidateCheck\.lean:\d+:\d+:")
_FP_WS_RE = re.compile(r"\s+")


def _normalize_details_fp(details: str) -> str:
    """Return a whitespace/line-number-agnostic fingerprint of a Lean error.

    Strips the leading `CandidateCheck.lean:LINE:COL:` markers and collapses
    all whitespace runs so two Lean runs that differ only in formatting
    noise produce the same fingerprint. Truncated to 512 chars — long
    enough to distinguish genuinely different errors, short enough that
    minor trailing-hint variation doesn't break the match.
    """
    if not details:
        return ""
    d = _FP_LINE_COL_RE.sub("", details)
    d = _FP_WS_RE.sub(" ", d).strip()
    return d[:512]


# Missing-olean errors can be infrastructure (a Benchmark dependency wasn't
# pre-built) or the model's fault (imported a module that doesn't exist). We
# only classify the former as environment_error so stagnation/temperature
# logic still applies to model-caused import mistakes.
# Lean prints both forms of this diagnostic, depending on context:
#   object file '<path>.olean' does not exist
#   object file '<path>.olean' of module <Name> does not exist
# so accept arbitrary text (incl. "of module <Name>") between the path and
# the "does not exist" tail.
_MISSING_OLEAN_RE = re.compile(
    r"object file ['\"]([^'\"]+\.olean)['\"]?[^\n]*?does not exist"
)
INFRA_ONLY_ERROR_PATTERNS = (
    re.compile(r"lean executable .* not found", re.IGNORECASE),
)


def _missing_olean_module(details: str) -> str | None:
    """Extract the module name whose .olean is missing, if the error is environmental."""
    match = _MISSING_OLEAN_RE.search(details)
    if not match:
        return None
    olean_path = match.group(1)
    # Strip any leading directories up to "Benchmark" (since paths may be absolute)
    marker = "/Benchmark/"
    idx = olean_path.rfind(marker)
    if idx >= 0:
        rel = olean_path[idx + 1 :]
    else:
        rel = olean_path
    if rel.endswith(".olean"):
        rel = rel[: -len(".olean")]
    return rel.replace("/", ".")


# Preflight failure_mode values that preflight_candidate returns. Used by
# _annotate_check_result to surface these as failure_class directly rather than
# collapsing them into "other" via English-language classify_failure lookup.
_PREFLIGHT_FAILURE_MODES = frozenset({
    "empty_response",
    "placeholder_detected",
    "hidden_proof_import_detected",
    "hidden_case_import_detected",
    "theorem_statement_mismatch",
})


def classify_failure(details: str) -> str:
    """Classify a Lean checker failure into a coarse category."""
    if not details:
        return "unknown"
    lower = details.lower()
    # Infrastructure errors that the model cannot reasonably be blamed for.
    for pattern in INFRA_ONLY_ERROR_PATTERNS:
        if pattern.search(details):
            return "environment_error"
    # Missing .olean is infra only when it is a Benchmark.* dependency *whose
    # source file actually exists* in the tree -- meaning lake should have
    # built it but didn't. If the source file is missing too, the model
    # imported / referenced something that doesn't exist, which is its own
    # mistake and should go through the normal stagnation/temperature loop.
    missing_module = _missing_olean_module(details)
    if missing_module and missing_module.startswith("Benchmark."):
        source_rel = Path(*missing_module.split(".")).with_suffix(".lean")
        if (ROOT / source_rel).is_file():
            return "environment_error"
    if "unknown identifier" in lower or "unknown constant" in lower:
        return "unknown_identifier"
    if "unsolved goals" in lower:
        return "unsolved_goals"
    if "application type mismatch" in lower or "function expected" in lower:
        return "type_error"
    if "type mismatch" in lower:
        return "type_mismatch"
    if "tactic 'split' failed" in details:
        return "split_failed"
    if "no goals to be solved" in details:
        return "no_goals"
    if "expected type must not contain free variables" in details:
        return "free_variables"
    if "declaration uses 'sorry'" in lower or "declaration uses 'admit'" in lower:
        return "placeholder"
    if "unknown tactic" in lower:
        return "unknown_tactic"
    if "simp made no progress" in lower:
        return "simp_no_progress"
    if "failed to unfold" in lower or ("unfold" in lower and "failed" in lower):
        return "unfold_failed"
    if "dsimp made no progress" in lower:
        return "simp_no_progress"
    if "tactic 'rfl' failed" in details:
        return "rfl_failed"
    if "invalid" in lower and "conv tactic" in lower:
        return "tactic_misuse"
    if "omega could not prove the goal" in lower:
        return "omega_failed"
    if "tactic 'constructor' failed" in details and "not an inductive datatype" in lower:
        return "constructor_failed"
    if "unknown module prefix" in lower:
        return "module_not_found"
    if "don't know how to synthesize placeholder" in lower:
        return "synthesis_failed"
    return "other"


def _build_check_hints(failure_class: str, details: str) -> list[str]:
    """Build targeted repair hints based on failure classification."""
    hints: list[str] = []
    if failure_class == "environment_error":
        hints.append(
            "ENVIRONMENT ERROR (not your fault): a dependency .olean is missing. "
            "The harness is attempting to rebuild it. If this persists, your proof is likely correct; "
            "retry run_lean_check once more."
        )
        return hints
    if failure_class == "placeholder_detected":
        hints.append(
            "PREFLIGHT REJECTED: proof contains `sorry` or `admit`. The harness "
            "will never accept these. Replace every `sorry`/`admit` with a real "
            "tactic, or use `?_` (unnamed hole) to probe a sub-goal with "
            "inspect_lean_goals / try_tactic_at_hole."
        )
        return hints
    if failure_class == "theorem_statement_mismatch":
        hints.append(
            "PREFLIGHT REJECTED: you changed the editable theorem signature. Only "
            "the proof body after `:=` is editable. Restore the exact theorem "
            "declaration from the original editable file (re-read it with "
            "read_public_file if unsure) and edit only the body."
        )
        return hints
    if failure_class == "hidden_proof_import_detected":
        hints.append(
            "PREFLIGHT REJECTED: proof imports a hidden `Benchmark.Cases.*.Proofs` "
            "module. Reference-solution modules are not part of the public API. "
            "Remove that import and write the proof yourself."
        )
        return hints
    if failure_class == "hidden_case_import_detected":
        hints.append(
            "PREFLIGHT REJECTED: proof imports a non-public `Benchmark.Cases.*` "
            "module. Only `Benchmark.Cases.*.Specs` (and your own editable file) "
            "are visible. Remove the blocked import."
        )
        return hints
    if failure_class == "empty_response":
        hints.append(
            "PREFLIGHT REJECTED: the proof content was empty. Submit the full "
            "Lean file including `import`, `namespace`, and the theorem with "
            "its proof body."
        )
        return hints
    if failure_class == "unknown_identifier":
        if "decide_True" in details or "decide_False" in details:
            hints.append("CRITICAL: `decide_True` and `decide_False` do not exist. Remove them. Instead, pass precondition hypotheses directly to `simp` - it handles `decide` reduction automatically.")
        else:
            hints.append("Use search_public_defs to find correct names from spec/impl files.")
        hints.append("Check imports. Standard names: Nat.lt_of_not_ge, Nat.not_le_of_lt.")
    elif failure_class == "unsolved_goals":
        hints.append("Use inspect_lean_goals with a ?_ hole to see exact goal state.")
        if "if " in details or "match" in details:
            hints.append("If simp leaves `if`/`match` with free variables, use `by_cases` on each unresolved condition BEFORE calling simp. Pass all case hypotheses to simp. Do NOT use `split` after simp or `native_decide`/`decide` on goals with free variables.")
        if "unused" in details.lower() and ("hBound" in details or "hypothesis" in details.lower()):
            hints.append("If a hypothesis is reported as unused by simp, try `simp_all` instead of `simp`. `simp_all` rewrites hypotheses into the goal, resolving mismatches between spec helper names and unfolded definitions.")
        hints.append("Try restructuring: `by_cases h : condition · simp [..., h] · simp [..., h]`.")
    elif failure_class == "type_mismatch":
        if "decide" in details:
            hints.append("The goal contains `decide` expressions. Pass all precondition hypotheses to `simp` and it will reduce `decide` automatically. Do NOT try to manually match `decide` types.")
        hints.append("Unfold definitions to align types. Check spec matches impl.")
    elif failure_class == "split_failed":
        hints.append("Do not split the post-state. Use by_cases with branch-specific helpers.")
    elif failure_class == "no_goals":
        hints.append("Previous simp closed the goal. Remove trailing tactics.")
    elif failure_class == "free_variables":
        hints.append("Reduce to concrete equalities before decide/native_decide.")
    elif failure_class == "unknown_tactic":
        hints.append("Use standard Lean 4 / Mathlib tactics only.")
    elif failure_class == "simp_no_progress":
        hints.append("simp/dsimp made no progress. CRITICAL: In each `by_cases` branch, you MUST repeat the FULL simp set (all contract definitions, storage fields, getStorage, setStorage, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, ContractResult.snd) PLUS the case hypothesis and all preconditions. Bare `simp [h]` will never work.")
        hints.append("Check that you are using the correct function name from the implementation file.")
    elif failure_class == "unfold_failed":
        hints.append("unfold failed. The definition name may be wrong or not unfoldable.")
        hints.append("Use search_public_defs to find the exact definition name.")
    elif failure_class == "rfl_failed":
        hints.append("rfl failed because the LHS is not definitionally equal to the RHS.")
        if "match" in details or "if " in details:
            hints.append("The goal has unresolved `if`/`match` expressions with free variables. Use `by_cases` on each condition BEFORE calling simp, not `split` after. Pass all case hypotheses to simp. For nested conditionals, nest `by_cases`. Example: `by_cases h : cond; · simp [..., h]; · simp [..., h]`.")
        else:
            hints.append("Try replacing `rfl` with `simp` or adding more definitions to the simp set.")
    elif failure_class == "tactic_misuse":
        hints.append("The tactic was used incorrectly for this goal shape.")
        hints.append("Check the goal state with inspect_lean_goals using a ?_ hole.")
    elif failure_class == "omega_failed":
        hints.append(
            "omega only handles LINEAR integer/natural arithmetic. It cannot close goals "
            "containing variable * variable, division, or modulus. Look at the "
            "counterexample section — any term on the RHS of `where` that mixes two "
            "variables multiplicatively, or uses `/` or `%`, is outside omega's reach."
        )
        nonlinear_hints: list[str] = []
        if "/" in details or "% " in details or " mod " in details:
            nonlinear_hints.append(
                "For division/modulus: first rewrite `a / b` and `a % b` via "
                "`Nat.div_add_mod` / `Nat.mul_div_cancel'` so omega sees a linear form, "
                "or case-split on whether the divisor is zero and handle each branch."
            )
        if "val *" in details or "* ↑" in details:
            nonlinear_hints.append(
                "For variable multiplications: introduce helper lemmas that bound the "
                "product (e.g. `Nat.mul_le_mul`), or try `nlinarith` / `positivity` which "
                "handle some nonlinear cases. Pure omega will never close a goal whose "
                "counterexample mentions a product of two symbolic `.val` terms."
            )
        hints.extend(nonlinear_hints)
    elif failure_class == "constructor_failed":
        hints.append(
            "`constructor` only works on inductive-type goals (And, Or, Exists, Sigma, "
            "structures). The goal you're targeting is an equality, implication, or an "
            "unreduced expression — not a constructor-shaped type. Either (a) `simp` / "
            "`unfold` first to expose an inductive head symbol, (b) `intro` pending "
            "hypotheses if the goal is `A → B`, or (c) use `refine ⟨_, _⟩` / "
            "`exact ⟨_, _⟩` if you already know the witnesses for an And/Exists."
        )
    elif failure_class == "module_not_found":
        hints.append(
            "The import path you requested is not available in this workspace. In "
            "particular, `Mathlib` is NOT a dependency of verity-benchmark — only the "
            "core Lean 4 prelude, `Batteries`, and the task's own `Benchmark.*` public "
            "modules are importable. Remove the offending `import` line and reach for "
            "core Lean / Batteries lemmas, or search_public_defs for existing helpers."
        )
    elif failure_class == "synthesis_failed":
        hints.append(
            "Lean could not infer a `_` / `?_` placeholder from context. Either (a) "
            "replace `_` with an explicit term, (b) add a `show <goal type>` line above "
            "the tactic so Lean knows the expected type, or (c) use `?_` (named hole) "
            "with `inspect_lean_goals` to see what Lean expected there before filling it."
        )
    return hints


def _build_repair_guidance(details: str) -> str:
    """Build structured repair guidance string from Lean error details (from main)."""
    hints: list[str] = []
    if "tactic 'split' failed" in details:
        hints.append(
            "- Do not `split` the final post-state blindly. Prove branch-specific helper theorems first, then use `by_cases` plus `simpa`."
        )
    if "no goals to be solved" in details:
        hints.append(
            "- A previous `simp` likely closed the goal already. Remove trailing tactics after the goal is solved."
        )
    if "expected type must not contain free variables" in details:
        hints.append(
            "- Do not use `native_decide` or `decide` on goals that still contain parameters. First reduce to concrete equalities."
        )
    if "unknown constant" in details or "Unknown identifier" in details or "unknown identifier" in details:
        hints.append(
            "- You are referencing a lemma or constant that does not exist in this Lean 4 environment. "
            "Do not guess lemma names. Instead, use `simp` with the relevant definitions, `omega` for arithmetic, "
            "or `decide`/`native_decide` for decidable propositions. Remove all references to unknown names."
        )
    if "unsolved goals" in details and "match" in details:
        hints.append(
            "- The remaining goal contains a `match` expression. Use `split` to case-split on the match, "
            "then solve each branch separately. If the match is on a ContractResult, try "
            "`simp only [...]` to reduce it first, or use `cases` on the matched expression."
        )
    if "unsolved goals" in details and "if " in details:
        hints.append(
            "- The remaining goal contains an `if` expression. Use `by_cases h : <condition>` to split on the condition, "
            "then `simp [h, ...]` in each branch. Alternatively, add the condition's hypothesis to the `simp` call."
        )
    if "unsolved goals" in details and "match" not in details and "if " not in details:
        hints.append(
            "- Unsolved goals remain. Check that `simp` is given all necessary definitions and hypotheses."
        )
    if "type mismatch" in details:
        hints.append(
            "- A type mismatch often means the proof term or tactic result does not match the goal. Re-read the spec and ensure your proof targets the correct type."
        )
    if "simp made no progress" in details:
        hints.append(
            "- `simp` made no progress with the given arguments. Add more definitions to unfold, "
            "or the simp arguments may already be fully reduced. Try removing the unproductive simp call."
        )
    if "failed to infer binder type" in details:
        hints.append(
            "- Lean cannot infer a binder type. Add explicit type annotations to your helper lemma parameters."
        )
    if "unexpected token" in details or "expected 'by'" in details:
        hints.append(
            "- Syntax error. Ensure the theorem body uses `:= by` followed by tactics. "
            "Do not use `:=` with a term-mode proof unless you are certain of the syntax."
        )
    if "Function expected at" in details or "unknown identifier" in details:
        hints.append(
            "- Use `s.storage 0` (function application) not `s.storage[0]` or `s.storage.0`. "
            "ContractState.storage is a function `Nat → Uint256`."
        )
    return "\n".join(hints)


def tool_result_json(result: dict[str, Any]) -> str:
    return json.dumps(result, indent=2, sort_keys=True)
