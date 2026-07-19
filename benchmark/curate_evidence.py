#!/usr/bin/env python3
"""Copy auditable benchmark artifacts while excluding model reasoning streams."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RESULTS_DIR = ROOT / "benchmark" / "results"
TASK_DIR = ROOT / "benchmark" / "tasks"
DEFAULT_DESTINATION = ROOT / "benchmark" / "evidence" / "2026-07-19-expanded"
MARKER = "__MODEL_COMPLETION__"
RUN_ID = re.compile(r"^\d{8}T\d{6}Z$")

INCLUDED_RUNS = (
    "20260719T201546Z",
    "20260719T201620Z",
    "20260719T204811Z",
    "20260719T204819Z",
    "20260719T204837Z",
    "20260719T205037Z",
    "20260719T205809Z",
    "20260719T210110Z",
    "20260719T210525Z",
    "20260719T211042Z",
    "20260719T211152Z",
    "20260719T211732Z",
    "20260719T213426Z",
)

EXCLUDED_RUNS = {
    "20260719T170134Z": "startup artifact with no metadata or completed trial",
    "20260719T170747Z": "startup artifact with no metadata or completed trial",
    "20260719T170846Z": (
        "superseded early gpt-5.4 repair pilot; not the preserved historical run"
    ),
    "20260719T172449Z": (
        "superseded early gpt-5.4 repair pilot; not the preserved historical run"
    ),
    "20260719T173519Z": "preserved separately in evidence/2026-07-19",
    "20260719T175249Z": "preserved separately in evidence/2026-07-19",
    "20260719T204756Z": (
        "rank-nullity finished, but the requested intermediate-value task did not"
    ),
    "20260719T204817Z": (
        "baseline finished, but the requested depth-4 task did not"
    ),
    "20260719T205024Z": (
        "baseline finished, but the requested depth-4 task did not"
    ),
    "20260719T213308Z": (
        "two matched-control trials finished, but the three-trial launcher was interrupted"
    ),
}

PROTOCOL_NOTES = [
    {
        "run_id": "20260719T205037Z",
        "task_id": "baseline_hahn_banach_available",
        "trial": 1,
        "note": (
            "Codex stderr recorded `patch rejected: empty patch`. No patch was "
            "applied and the returned proof compiled, but this trial is not "
            "strictly free of attempted tool activity."
        ),
    }
]


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def copy_file(source: Path, target: Path) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)


def require_hash(path: Path, expected: str | None, label: str) -> None:
    if expected is not None and file_sha256(path) != expected:
        raise RuntimeError(f"{label} SHA-256 mismatch: {path}")


def completion_from_source(source_path: Path, task_id: str) -> str:
    template = (TASK_DIR / f"{task_id}.lean.in").read_text(encoding="utf-8")
    prefix, suffix = template.split(MARKER, 1)
    source = source_path.read_text(encoding="utf-8")
    if not source.startswith(prefix) or not source.endswith(suffix):
        raise RuntimeError(f"source does not match task template: {source_path}")
    return source[len(prefix) : len(source) - len(suffix)]


def validate_result_artifacts(
    result_path: Path,
    result: dict,
    summary_result: dict,
    metadata: dict,
) -> None:
    task_id = result_path.parent.parent.name
    trial_name = result_path.parent.name
    expected_trial_name = f"trial_{result['trial']}"
    if result["task_id"] != task_id or trial_name != expected_trial_name:
        raise RuntimeError(f"result path identity mismatch: {result_path}")
    if task_id not in metadata["tasks"]:
        raise RuntimeError(f"result task is absent from metadata: {result_path}")
    if result != summary_result:
        raise RuntimeError(f"result does not match summary object: {result_path}")

    attempts = result["attempts"]
    if result["attempts_used"] != len(attempts) or not attempts:
        raise RuntimeError(f"invalid attempt count: {result_path}")
    if [attempt["attempt"] for attempt in attempts] != list(
        range(1, len(attempts) + 1)
    ):
        raise RuntimeError(f"attempt sequence is not contiguous: {result_path}")
    if result["passed"] != bool(attempts[-1]["compiled"]):
        raise RuntimeError(f"result pass flag is inconsistent: {result_path}")
    if any(attempt["compiled"] for attempt in attempts[:-1]):
        raise RuntimeError(f"run continued after a passing attempt: {result_path}")

    trial_dir = result_path.parent
    for attempt in attempts:
        number = attempt["attempt"]
        compiled = bool(attempt["compiled"])
        validation_error = attempt.get("validation_error")
        if compiled and validation_error is not None:
            raise RuntimeError(
                f"passing attempt has a validation error: {result_path} #{number}"
            )

        diagnostic = trial_dir / f"attempt_{number}_diagnostic.txt"
        if not diagnostic.is_file():
            raise RuntimeError(f"missing diagnostic: {diagnostic}")
        require_hash(
            diagnostic,
            attempt.get("diagnostic_sha256"),
            "diagnostic",
        )

        source = trial_dir / f"attempt_{number}.lean"
        source_required = compiled or validation_error is None
        if source_required and not source.is_file():
            raise RuntimeError(f"missing assembled Lean source: {source}")
        if source.is_file():
            require_hash(source, attempt.get("source_sha256"), "source")
            completion = completion_from_source(source, task_id)
            completion_hash = attempt.get("completion_sha256")
            if (
                completion_hash is not None
                and hashlib.sha256(completion.encode("utf-8")).hexdigest()
                != completion_hash
            ):
                raise RuntimeError(f"completion SHA-256 mismatch: {source}")

        response = trial_dir / f"attempt_{number}_response.json"
        if not response.is_file():
            raise RuntimeError(f"missing raw response at curation time: {response}")
        require_hash(
            response,
            attempt.get("raw_response_sha256"),
            "raw response",
        )


def copy_run(run_id: str, destination: Path) -> dict:
    if not RUN_ID.fullmatch(run_id):
        raise ValueError(f"invalid run id: {run_id}")
    source_dir = RESULTS_DIR / run_id
    if not source_dir.is_dir():
        raise FileNotFoundError(source_dir)
    target_dir = destination / "runs" / run_id

    metadata_path = source_dir / "metadata.json"
    summary_path = source_dir / "summary.json"
    if not metadata_path.is_file() or not summary_path.is_file():
        raise RuntimeError(f"{run_id} is incomplete: metadata or summary is missing")
    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    if summary.get("status") != "completed":
        raise RuntimeError(f"{run_id} has non-completed status: {summary.get('status')}")
    if summary.get("infrastructure_failures"):
        raise RuntimeError(f"{run_id} contains infrastructure failures")

    result_paths = sorted(source_dir.glob("*/trial_*/result.json"))
    if len(result_paths) != summary.get("total_completed"):
        raise RuntimeError(
            f"{run_id}: result count does not match completed summary count"
        )
    summary_results = {
        (result["task_id"], result["trial"]): result
        for result in summary["results"]
    }
    if len(summary["results"]) != summary["total_completed"]:
        raise RuntimeError(f"{run_id}: summary result count is inconsistent")
    if len(summary_results) != len(summary["results"]):
        raise RuntimeError(f"{run_id}: summary result identities are not unique")

    copy_file(metadata_path, target_dir / "metadata.json")
    copy_file(summary_path, target_dir / "summary.json")
    passed = 0
    for result_path in result_paths:
        result = json.loads(result_path.read_text(encoding="utf-8"))
        key = (result["task_id"], result["trial"])
        if key not in summary_results:
            raise RuntimeError(f"result is absent from summary: {result_path}")
        validate_result_artifacts(
            result_path,
            result,
            summary_results[key],
            metadata,
        )
        passed += int(result["passed"])
        relative = result_path.relative_to(source_dir)
        copy_file(result_path, target_dir / relative)
        trial_dir = result_path.parent
        for attempt in result["attempts"]:
            number = attempt["attempt"]
            diagnostic = trial_dir / f"attempt_{number}_diagnostic.txt"
            copy_file(diagnostic, target_dir / diagnostic.relative_to(source_dir))
            source = trial_dir / f"attempt_{number}.lean"
            if source.is_file():
                copy_file(source, target_dir / source.relative_to(source_dir))

    if passed != summary["passed"]:
        raise RuntimeError(f"{run_id}: summary pass count is inconsistent")
    return {
        "run_id": run_id,
        "model": metadata["model"],
        "tasks": metadata["tasks"],
        "max_attempts": metadata["max_attempts"],
        "passed": summary["passed"],
        "total_completed": summary["total_completed"],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--run", action="append", dest="runs")
    parser.add_argument(
        "--destination", type=Path, default=DEFAULT_DESTINATION
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    destination = args.destination.resolve()
    evidence_root = (ROOT / "benchmark" / "evidence").resolve()
    if evidence_root not in destination.parents:
        raise RuntimeError("destination must be below benchmark/evidence")
    if destination.exists():
        raise RuntimeError(f"destination already exists: {destination}")

    requested_runs = tuple(args.runs or INCLUDED_RUNS)
    if set(requested_runs) != set(INCLUDED_RUNS) or len(requested_runs) != len(
        INCLUDED_RUNS
    ):
        raise RuntimeError("curation requires the exact reported run registry")
    discovered_runs = {
        path.name
        for path in RESULTS_DIR.iterdir()
        if path.is_dir() and RUN_ID.fullmatch(path.name)
    }
    classified_runs = set(INCLUDED_RUNS) | set(EXCLUDED_RUNS)
    if discovered_runs != classified_runs:
        raise RuntimeError(
            "result directory registry mismatch: "
            f"unclassified={sorted(discovered_runs - classified_runs)}, "
            f"missing={sorted(classified_runs - discovered_runs)}"
        )

    destination.mkdir(parents=True)
    runs = [copy_run(run_id, destination) for run_id in requested_runs]
    forbidden = list(destination.rglob("*_response.json"))
    if forbidden:
        raise RuntimeError(f"raw response artifacts were copied: {forbidden}")

    files = []
    for path in sorted(item for item in destination.rglob("*") if item.is_file()):
        files.append(
            {
                "path": path.relative_to(destination).as_posix(),
                "bytes": path.stat().st_size,
                "sha256": file_sha256(path),
            }
        )
    manifest = {
        "format": 2,
        "curator_sha256": file_sha256(Path(__file__).resolve()),
        "runs": runs,
        "excluded_runs": EXCLUDED_RUNS,
        "protocol_notes": PROTOCOL_NOTES,
        "raw_model_responses_included": False,
        "source_consistency_checks": (
            "summary/result identity, attempt invariants, and every stored "
            "source/diagnostic/completion/raw-response hash were checked before copy"
        ),
        "files": files,
    }
    (destination / "manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"Curated {len(runs)} runs and {len(files)} hashed files")
    print(destination.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
