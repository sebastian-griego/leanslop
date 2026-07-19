#!/usr/bin/env python3
"""Recheck the curated model completions with the current hardened verifier."""

from __future__ import annotations

import tempfile
from pathlib import Path

import run_benchmark as runner


EVIDENCE_DIR = Path(__file__).resolve().parent / "evidence" / "2026-07-19"
CASES = (
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


def task_by_id(task_id: str) -> runner.Task:
    return next(task for task in runner.TASKS if task.task_id == task_id)


def render_with_current_verifier(
    evidence_path: Path, task: runner.Task, historical_axiom_report: str
) -> str:
    template = task.path.read_text(encoding="utf-8")
    prefix = template.split(runner.MARKER, 1)[0]
    historical_source = evidence_path.read_text(encoding="utf-8")
    if not historical_source.startswith(prefix):
        raise RuntimeError(f"{evidence_path} does not match the current task prefix")
    report_offset = historical_source.find(historical_axiom_report, len(prefix))
    if report_offset < 0:
        raise RuntimeError(f"{evidence_path} lacks its historical axiom report")
    completion = historical_source[len(prefix) : report_offset].strip() + "\n"
    return template.replace(runner.MARKER, completion)


def main() -> int:
    failures = []
    with tempfile.TemporaryDirectory(prefix="leanslop_evidence_") as temporary:
        temporary_dir = Path(temporary)
        for filename, task_id, old_report, expected_pass in CASES:
            task = task_by_id(task_id)
            evidence_path = EVIDENCE_DIR / filename
            rendered = render_with_current_verifier(evidence_path, task, old_report)
            source_path = temporary_dir / filename
            source_path.write_text(rendered, encoding="utf-8")
            passed, diagnostic, _ = runner.compile_source(task, source_path)
            print(f"{filename}: {'PASS' if passed else 'FAIL'}")
            if passed != expected_pass:
                failures.append(f"{filename}\n{diagnostic}")
    if failures:
        print("\n\n".join(failures))
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
