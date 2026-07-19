#!/usr/bin/env python3
"""Compile canonical mathlib proofs against every benchmark template."""

from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path

import run_benchmark as runner


MATHLIB_ROOT = runner.ROOT / ".lake" / "packages" / "mathlib" / "Mathlib"
EXTENSION_SOURCE = (
    MATHLIB_ROOT / "Analysis" / "Convex" / "Cone" / "Extension.lean"
)
FINITE_DIMENSIONAL_SOURCE = (
    MATHLIB_ROOT / "LinearAlgebra" / "FiniteDimensional" / "Lemmas.lean"
)
INTERMEDIATE_VALUE_SOURCE = (
    MATHLIB_ROOT / "Topology" / "Order" / "IntermediateValue.lean"
)
HAHN_IMPORTS = """\
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.LinearPMap
"""
RANK_NULLITY_IMPORTS = """\
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
"""
INTERMEDIATE_VALUE_IMPORTS = """\
import Mathlib.Order.Interval.Set.Image
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Connected.TotallyDisconnected
"""
REDACTION_PROBES = (
    (
        HAHN_IMPORTS,
        (
            "exists_extension_of_le_sublinear",
            "riesz_extension",
            "RieszExtension.exists_top",
            "RieszExtension.step",
        ),
    ),
    (
        RANK_NULLITY_IMPORTS,
        ("LinearMap.finrank_range_add_finrank_ker",),
    ),
    (
        INTERMEDIATE_VALUE_IMPORTS,
        (
            "intermediate_value_univ₂",
            "IsPreconnected.intermediate_value₂",
            "IsPreconnected.intermediate_value",
        ),
    ),
)


def between(source: str, start: str, end: str) -> str:
    start_offset = source.index(start)
    end_offset = source.index(end, start_offset)
    return source[start_offset:end_offset].strip() + "\n"


def reference_completions() -> dict[str, str]:
    extension_source = EXTENSION_SOURCE.read_text(encoding="utf-8")
    step = between(extension_source, "theorem step", "\ntheorem exists_top")
    exists_top = between(
        extension_source, "theorem exists_top", "\nend RieszExtension"
    )
    riesz = between(
        extension_source,
        "theorem riesz_extension",
        "\n/-- **Hahn-Banach theorem**",
    )
    hahn = (
        extension_source[
            extension_source.index("theorem exists_extension_of_le_sublinear") :
        ].strip()
        + "\n"
    )
    hahn_signature = hahn.split(" := by", 1)[0]
    baseline_hahn = (
        hahn_signature.replace(
            "theorem exists_extension_of_le_sublinear",
            "theorem tested_hahn_banach",
            1,
        )
        + " := exists_extension_of_le_sublinear f N N_hom N_add hf\n"
    )

    finite_source = FINITE_DIMENSIONAL_SOURCE.read_text(encoding="utf-8")
    rank_nullity = between(
        finite_source,
        "theorem finrank_range_add_finrank_ker",
        "\nlemma ker_ne_bot_of_finrank_lt",
    ).replace(
        "theorem finrank_range_add_finrank_ker",
        "theorem tested_rank_nullity",
        1,
    )

    intermediate_source = INTERMEDIATE_VALUE_SOURCE.read_text(encoding="utf-8")
    intermediate_univ = between(
        intermediate_source,
        "theorem intermediate_value_univ₂",
        "\ntheorem intermediate_value_univ₂_eventually₁",
    ).replace(
        "theorem intermediate_value_univ₂",
        "theorem local_intermediate_value_univ₂",
        1,
    )
    intermediate_on_set = between(
        intermediate_source,
        "theorem IsPreconnected.intermediate_value₂",
        "\ntheorem IsPreconnected.intermediate_value₂_eventually₁",
    ).replace(
        "theorem IsPreconnected.intermediate_value₂",
        "theorem local_intermediate_value₂",
        1,
    ).replace(
        "@intermediate_value_univ₂",
        "@local_intermediate_value_univ₂",
    )
    intermediate_value = between(
        intermediate_source,
        "theorem IsPreconnected.intermediate_value {",
        "\ntheorem IsPreconnected.intermediate_value_Ico",
    ).replace(
        "theorem IsPreconnected.intermediate_value",
        "theorem tested_intermediate_value",
        1,
    ).replace(
        "hs.intermediate_value₂",
        "local_intermediate_value₂ hs",
    )

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
        "baseline_hahn_banach_available": baseline_hahn,
        "control_hahn_banach_premise_available": (
            hahn_signature.replace(
                "theorem exists_extension_of_le_sublinear",
                "theorem tested_hahn_banach",
                1,
            )
            + " := provided_hahn_banach f N N_hom N_add hf\n"
        ),
        "rank_nullity_target_redacted": rank_nullity,
        "intermediate_value_interfaces_redacted": (
            intermediate_univ + "\n" + intermediate_on_set + "\n" + intermediate_value
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
        probe_number = 0
        for imports, declarations in REDACTION_PROBES:
            for declaration in declarations:
                probe_number += 1
                display_name = declaration.encode("ascii", "backslashreplace").decode()
                probe_path = temporary_dir / f"probe_{probe_number}.lean"
                probe_path.write_text(
                    f"{imports}\n#check {declaration}\n",
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
                probe_output = probe.stdout + probe.stderr
                absent = probe.returncode != 0 and "lean.unknownIdentifier" in probe_output
                print(f"{display_name}: {'ABSENT' if absent else 'AVAILABLE'}")
                if not absent:
                    failures.append(
                        f"{declaration} was unexpectedly available\n"
                        f"{probe_output}"
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
