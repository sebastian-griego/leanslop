#!/usr/bin/env python3
"""Recheck curated completions and the integrity of their evidence manifests."""

from __future__ import annotations

import hashlib
import json
import tempfile
from pathlib import Path

import curate_evidence as curator
import run_benchmark as runner


EVIDENCE_ROOT = Path(__file__).resolve().parent / "evidence"
LEGACY_DIR = EVIDENCE_ROOT / "2026-07-19"
EXPANDED_DIR = EVIDENCE_ROOT / "2026-07-19-expanded"
LEGACY_CASES = (
    (
        "control_attempt_1.lean",
        "control_shallow_algebra",
        "#print axioms tested_shallow_control",
        True,
    ),
    (
        "depth1_attempt_1.lean",
        "depth1_riesz_available",
        "#print axioms tested_hahn_banach",
        False,
    ),
    (
        "depth1_attempt_2.lean",
        "depth1_riesz_available",
        "#print axioms tested_hahn_banach",
        False,
    ),
    (
        "depth1_attempt_3.lean",
        "depth1_riesz_available",
        "#print axioms tested_hahn_banach",
        False,
    ),
)
LEGACY_HASHES = {
    "control_attempt_1.lean": (
        "b4e4c94b2f2161d5a11c7d373b81d8e11d30b3cc26152bd05cd102951adb5deb"
    ),
    "control_run_summary.json": (
        "35b095425dd22f6e1faefc7fe6fb92b17cf461c50af89851ea13a0b117901313"
    ),
    "depth1_attempt_1.lean": (
        "11112987b42476e3cd0006cd514269c3a149f284bda44b907329178c7c864ef6"
    ),
    "depth1_attempt_2.lean": (
        "d2e6317d49860593c4d64772363cbbd3f3bff2def3937e5502519b9596594289"
    ),
    "depth1_attempt_3.lean": (
        "2098758196f7a6749702bc379a49713083083ef37147d2ec25572c4bf0e3b59a"
    ),
    "depth1_run_summary.json": (
        "f503136dfbc01fa318fc2ce729d1a588ab30f2e30ccdc1c3087845b6871d94a3"
    ),
}


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def task_by_id(task_id: str) -> runner.Task:
    return next(task for task in runner.TASKS if task.task_id == task_id)


def completion_from_current_source(source: str, task: runner.Task) -> str:
    template = task.path.read_text(encoding="utf-8")
    prefix, suffix = template.split(runner.MARKER, 1)
    if not source.startswith(prefix) or not source.endswith(suffix):
        raise RuntimeError(
            f"assembled source does not match current template: {task.task_id}"
        )
    suffix_start = len(source) - len(suffix)
    return source[len(prefix) : suffix_start]


def render_legacy_with_current_verifier(
    evidence_path: Path, task: runner.Task, historical_axiom_report: str
) -> tuple[str, str]:
    template = task.path.read_text(encoding="utf-8")
    prefix = template.split(runner.MARKER, 1)[0]
    historical_source = evidence_path.read_text(encoding="utf-8")
    if not historical_source.startswith(prefix):
        raise RuntimeError(f"{evidence_path} does not match the current task prefix")
    if historical_source.count(historical_axiom_report) != 1:
        raise RuntimeError(
            f"{evidence_path} must contain exactly one historical axiom report"
        )
    report_offset = historical_source.index(
        historical_axiom_report, len(prefix)
    )
    completion = historical_source[len(prefix) : report_offset].strip() + "\n"
    return template.replace(runner.MARKER, completion), completion


def verify_manifest() -> tuple[dict, list[str]]:
    failures = []
    manifest_path = EXPANDED_DIR / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if manifest.get("format") != 2:
        failures.append("expanded evidence does not use manifest format 2")
    if manifest.get("curator_sha256") != file_sha256(Path(curator.__file__)):
        failures.append("manifest curator SHA-256 does not match current curator")
    manifest_run_ids = tuple(run["run_id"] for run in manifest["runs"])
    if set(manifest_run_ids) != set(curator.INCLUDED_RUNS):
        failures.append("manifest included-run registry mismatch")
    if manifest.get("excluded_runs") != curator.EXCLUDED_RUNS:
        failures.append("manifest excluded-run registry mismatch")
    if manifest.get("raw_model_responses_included") is not False:
        failures.append("manifest does not explicitly exclude raw model responses")
    if list(EXPANDED_DIR.rglob("*_response.json")):
        failures.append("expanded evidence contains raw response artifacts")

    expected_paths = {item["path"] for item in manifest["files"]}
    actual_paths = {
        path.relative_to(EXPANDED_DIR).as_posix()
        for path in EXPANDED_DIR.rglob("*")
        if path.is_file() and path != manifest_path
    }
    if expected_paths != actual_paths:
        failures.append(
            "manifest file set mismatch: "
            f"missing={sorted(expected_paths - actual_paths)}, "
            f"extra={sorted(actual_paths - expected_paths)}"
        )
    for item in manifest["files"]:
        path = (EXPANDED_DIR / item["path"]).resolve()
        if EXPANDED_DIR.resolve() not in path.parents:
            failures.append(f"manifest path escapes evidence root: {item['path']}")
            continue
        if not path.is_file():
            continue
        if path.stat().st_size != item["bytes"]:
            failures.append(f"byte-size mismatch: {item['path']}")
        if file_sha256(path) != item["sha256"]:
            failures.append(f"SHA-256 mismatch: {item['path']}")
    return manifest, failures


def verify_legacy(temporary_dir: Path) -> list[str]:
    failures = []
    actual_files = {path.name for path in LEGACY_DIR.iterdir() if path.is_file()}
    if actual_files != set(LEGACY_HASHES):
        failures.append(
            "legacy evidence file set mismatch: "
            f"missing={sorted(set(LEGACY_HASHES) - actual_files)}, "
            f"extra={sorted(actual_files - set(LEGACY_HASHES))}"
        )
    for filename, expected_hash in LEGACY_HASHES.items():
        path = LEGACY_DIR / filename
        if path.is_file() and file_sha256(path) != expected_hash:
            failures.append(f"legacy SHA-256 mismatch: {filename}")

    for filename, task_id, old_report, expected_pass in LEGACY_CASES:
        task = task_by_id(task_id)
        evidence_path = LEGACY_DIR / filename
        rendered, completion = render_legacy_with_current_verifier(
            evidence_path, task, old_report
        )
        if validation_error := runner.validate_task_completion(task, completion):
            failures.append(f"{filename}: {validation_error}")
            continue
        source_path = temporary_dir / f"legacy_{filename}"
        source_path.write_text(rendered, encoding="utf-8")
        passed, diagnostic, _ = runner.compile_source(task, source_path)
        print(f"legacy/{filename}: {'PASS' if passed else 'FAIL'}")
        if passed != expected_pass:
            failures.append(f"{filename}\n{diagnostic}")
    return failures


def verify_expanded(manifest: dict) -> list[str]:
    failures = []
    checked_attempts = 0
    expected_result_count = sum(run["total_completed"] for run in manifest["runs"])
    expected_run_ids = {run["run_id"] for run in manifest["runs"]}
    actual_run_ids = {
        path.name for path in (EXPANDED_DIR / "runs").iterdir() if path.is_dir()
    }
    if actual_run_ids != expected_run_ids:
        failures.append(
            "curated run directory mismatch: "
            f"missing={sorted(expected_run_ids - actual_run_ids)}, "
            f"extra={sorted(actual_run_ids - expected_run_ids)}"
        )
    result_paths = sorted(EXPANDED_DIR.glob("runs/*/*/trial_*/result.json"))
    if len(result_paths) != expected_result_count:
        failures.append(
            f"expected {expected_result_count} result files, found {len(result_paths)}"
        )

    manifest_runs = {run["run_id"]: run for run in manifest["runs"]}
    results_by_run: dict[str, list[tuple[Path, dict]]] = {
        run_id: [] for run_id in expected_run_ids
    }
    for result_path in result_paths:
        result = json.loads(result_path.read_text(encoding="utf-8"))
        run_id = result_path.parents[2].name
        results_by_run.setdefault(run_id, []).append((result_path, result))

    for run_id, run_results in results_by_run.items():
        run_dir = EXPANDED_DIR / "runs" / run_id
        metadata = json.loads((run_dir / "metadata.json").read_text(encoding="utf-8"))
        summary = json.loads((run_dir / "summary.json").read_text(encoding="utf-8"))
        manifest_run = manifest_runs[run_id]
        expected_manifest_run = {
            "run_id": run_id,
            "model": metadata["model"],
            "tasks": metadata["tasks"],
            "max_attempts": metadata["max_attempts"],
            "passed": summary["passed"],
            "total_completed": summary["total_completed"],
        }
        if manifest_run != expected_manifest_run:
            failures.append(f"manifest run metadata mismatch: {run_id}")
        if summary.get("status") != "completed" or summary.get(
            "infrastructure_failures"
        ):
            failures.append(f"run is not cleanly completed: {run_id}")
        if len(run_results) != summary["total_completed"]:
            failures.append(f"run result count mismatch: {run_id}")
        summary_results = {
            (result["task_id"], result["trial"]): result
            for result in summary["results"]
        }
        if len(summary["results"]) != summary["total_completed"]:
            failures.append(f"summary result count is inconsistent: {run_id}")
        if len(summary_results) != len(summary["results"]):
            failures.append(f"summary result identities are not unique: {run_id}")

        run_passed = 0
        for result_path, result in run_results:
            key = (result["task_id"], result["trial"])
            if summary_results.get(key) != result:
                failures.append(f"result/summary mismatch: {result_path}")
            if result_path.parent.parent.name != result["task_id"]:
                failures.append(f"result task/path mismatch: {result_path}")
            if result_path.parent.name != f"trial_{result['trial']}":
                failures.append(f"result trial/path mismatch: {result_path}")
            if result["task_id"] not in metadata["tasks"]:
                failures.append(f"result task absent from metadata: {result_path}")
            run_passed += int(result["passed"])

            attempts = result["attempts"]
            if not attempts or result["attempts_used"] != len(attempts):
                failures.append(f"invalid attempt count: {result_path}")
                continue
            if [attempt["attempt"] for attempt in attempts] != list(
                range(1, len(attempts) + 1)
            ):
                failures.append(f"non-contiguous attempts: {result_path}")
            if any(attempt["compiled"] for attempt in attempts[:-1]):
                failures.append(f"run continued after passing: {result_path}")
            expected_pass = bool(attempts[-1]["compiled"])
            if result["passed"] != expected_pass:
                failures.append(f"result consistency failure: {result_path}")

            for attempt in attempts:
                checked_attempts += 1
                number = attempt["attempt"]
                compiled_recorded = bool(attempt["compiled"])
                validation_error = attempt.get("validation_error")
                if compiled_recorded and validation_error is not None:
                    failures.append(
                        f"passing attempt has validation error: {result_path} #{number}"
                    )

                diagnostic_path = (
                    result_path.parent / f"attempt_{number}_diagnostic.txt"
                )
                if not diagnostic_path.is_file():
                    failures.append(f"missing diagnostic: {diagnostic_path}")
                elif (
                    attempt.get("diagnostic_sha256") is not None
                    and file_sha256(diagnostic_path)
                    != attempt["diagnostic_sha256"]
                ):
                    failures.append(
                        f"stored diagnostic SHA-256 mismatch: {diagnostic_path}"
                    )

                source_path = result_path.parent / f"attempt_{number}.lean"
                source_required = compiled_recorded or validation_error is None
                if source_required and not source_path.is_file():
                    failures.append(f"missing source: {source_path}")
                    continue
                if not source_path.is_file():
                    continue
                if (
                    attempt.get("source_sha256") is not None
                    and file_sha256(source_path) != attempt["source_sha256"]
                ):
                    failures.append(f"stored source SHA-256 mismatch: {source_path}")

                source = source_path.read_text(encoding="utf-8")
                try:
                    completion = completion_from_current_source(source, task_by_id(result["task_id"]))
                except (RuntimeError, StopIteration) as error:
                    failures.append(f"{source_path}: {error}")
                    continue
                if (
                    attempt.get("completion_sha256") is not None
                    and hashlib.sha256(completion.encode("utf-8")).hexdigest()
                    != attempt["completion_sha256"]
                ):
                    failures.append(
                        f"stored completion SHA-256 mismatch: {source_path}"
                    )
                task = task_by_id(result["task_id"])
                if validation_error_now := runner.validate_task_completion(
                    task, completion
                ):
                    failures.append(f"{source_path}: {validation_error_now}")
                    continue

                compiled, diagnostic, _ = runner.compile_source(task, source_path)
                if compiled != compiled_recorded:
                    failures.append(
                        f"{source_path}: expected compiled={compiled_recorded}, "
                        f"got {compiled}\n{diagnostic}"
                    )

        if run_passed != summary["passed"]:
            failures.append(f"run pass count mismatch: {run_id}")

    print(
        f"expanded evidence: {len(result_paths)} trials, "
        f"{checked_attempts} attempts rechecked"
    )
    return failures


def main() -> int:
    manifest, failures = verify_manifest()
    with tempfile.TemporaryDirectory(prefix="leanslop_evidence_") as temporary:
        failures.extend(verify_legacy(Path(temporary)))
    failures.extend(verify_expanded(manifest))
    if failures:
        print("\n\n".join(failures))
        return 1
    print("Evidence hashes, static policy, compilation, and axiom closure verified.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
