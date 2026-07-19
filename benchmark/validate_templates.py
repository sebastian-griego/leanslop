#!/usr/bin/env python3
"""Compile canonical mathlib proofs against every benchmark template."""

from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path

import run_benchmark as runner


EXTENSION_SOURCE = (
    runner.ROOT
    / ".lake"
    / "packages"
    / "mathlib"
    / "Mathlib"
    / "Analysis"
    / "Convex"
    / "Cone"
    / "Extension.lean"
)
NARROW_IMPORTS = """\
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.LinearPMap
"""
REDACTED_DECLARATIONS = (
    "exists_extension_of_le_sublinear",
    "riesz_extension",
    "RieszExtension.exists_top",
    "RieszExtension.step",
)


def between(source: str, start: str, end: str) -> str:
    start_offset = source.index(start)
    end_offset = source.index(end, start_offset)
    return source[start_offset:end_offset].strip() + "\n"


def reference_completions() -> dict[str, str]:
    source = EXTENSION_SOURCE.read_text(encoding="utf-8")
    step = between(source, "theorem step", "\ntheorem exists_top")
    exists_top = between(source, "theorem exists_top", "\nend RieszExtension")
    riesz = between(
        source,
        "theorem riesz_extension",
        "\n/-- **Hahn-Banach theorem**",
    )
    hahn = source[source.index("theorem exists_extension_of_le_sublinear") :].strip() + "\n"

    local_step = step.replace("theorem step", "theorem local_step", 1)
    local_exists_from_step = exists_top.replace(
        "theorem exists_top", "theorem local_exists_top", 1
    ).replace("rcases step s q", "rcases local_step s q")
    local_exists_from_provider = exists_top.replace(
        "theorem exists_top", "theorem local_exists_top", 1
    ).replace("rcases step s q", "rcases provided_step s q")
    local_riesz_from_exists = riesz.replace(
        "theorem riesz_extension", "theorem local_riesz_extension", 1
    ).replace("RieszExtension.exists_top", "local_exists_top")
    local_riesz_from_provider = riesz.replace(
        "theorem riesz_extension", "theorem local_riesz_extension", 1
    ).replace("RieszExtension.exists_top", "provided_exists_top")
    tested_from_local_riesz = hahn.replace(
        "theorem exists_extension_of_le_sublinear",
        "theorem tested_hahn_banach",
        1,
    ).replace("riesz_extension", "local_riesz_extension")
    tested_from_provider = hahn.replace(
        "theorem exists_extension_of_le_sublinear",
        "theorem tested_hahn_banach",
        1,
    ).replace("riesz_extension", "provided_riesz_extension")

    section_s = "variable (s : PointedCone ℝ E)\n"
    section_s_f = "variable (s : PointedCone ℝ E) (f : E →ₗ.[ℝ] ℝ)\n"
    return {
        "control_shallow_algebra": (
            "theorem tested_shallow_control (x y : ℝ) : "
            "2 * x * y ≤ x ^ 2 + y ^ 2 := by\n"
            "  nlinarith [sq_nonneg (x - y)]\n"
        ),
        "depth1_riesz_available": tested_from_provider,
        "depth2_maximal_extension_available": (
            local_riesz_from_provider + "\n" + tested_from_local_riesz
        ),
        "depth3_one_step_available": (
            section_s
            + local_exists_from_provider
            + "\n"
            + local_riesz_from_exists
            + "\n"
            + tested_from_local_riesz
        ),
        "depth4_no_scaffold": (
            section_s_f
            + local_step
            + "\n"
            + local_exists_from_step
            + "\n"
            + local_riesz_from_exists
            + "\n"
            + tested_from_local_riesz
        ),
    }


def main() -> int:
    completions = reference_completions()
    failures = []
    with tempfile.TemporaryDirectory(prefix="leanslop_references_") as temporary:
        temporary_dir = Path(temporary)
        for declaration in REDACTED_DECLARATIONS:
            probe_path = temporary_dir / f"probe_{declaration.replace('.', '_')}.lean"
            probe_path.write_text(
                f"{NARROW_IMPORTS}\n#check {declaration}\n",
                encoding="utf-8",
            )
            probe = subprocess.run(
                ["lake", "env", "lean", str(probe_path)],
                cwd=runner.ROOT,
                text=True,
                encoding="utf-8",
                errors="replace",
                capture_output=True,
                timeout=180,
                check=False,
            )
            absent = probe.returncode != 0 and "Unknown identifier" in (
                probe.stdout + probe.stderr
            )
            print(f"{declaration}: {'ABSENT' if absent else 'AVAILABLE'}")
            if not absent:
                failures.append(
                    f"{declaration} was unexpectedly available\n"
                    f"{probe.stdout}{probe.stderr}"
                )
        for task in runner.TASKS:
            template = task.path.read_text(encoding="utf-8")
            source = template.replace(runner.MARKER, completions[task.task_id])
            source_path = temporary_dir / f"{task.task_id}.lean"
            source_path.write_text(source, encoding="utf-8")
            passed, diagnostic, _ = runner.compile_source(task, source_path)
            print(f"{task.task_id}: {'PASS' if passed else 'FAIL'}")
            if not passed:
                failures.append(f"{task.task_id}\n{diagnostic}")
    if failures:
        print("\n\n".join(failures))
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
