#!/usr/bin/env python3
"""Focused regression tests for benchmark policy and verifier parsing."""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_benchmark as runner
import validate_templates


class HarnessPolicyTests(unittest.TestCase):
    def test_reference_completions_pass_static_policy(self) -> None:
        completions = validate_templates.reference_completions()
        for task in runner.TASKS:
            with self.subTest(task=task.task_id):
                self.assertIsNone(
                    runner.validate_task_completion(
                        task, completions[task.task_id]
                    )
                )

    def test_meta_and_output_escapes_are_rejected(self) -> None:
        completions = (
            "theorem tested_shallow_control : True := by native_decide",
            "theorem tested_shallow_control : True := by run_tac pure ()",
            "theorem tested_shallow_control : True := unsafeCast 0",
            "#eval IO.getEnv \"SECRET\"",
            "set_option pp.all true in\n"
            "theorem tested_shallow_control : True := by trivial",
            "macro \"answer\" : term => `(True)",
            "local macro \"answer\" : term => `(True)",
            "local syntax \"answer\" : term",
            "local elab \"answer\" : term => pure (mkIdent `True)",
            "include_str \"Mathlib/Hidden.lean\"",
        )
        for completion in completions:
            with self.subTest(completion=completion):
                self.assertIsNotNone(runner.validate_completion(completion))

    def test_task_declaration_is_required_exactly_once(self) -> None:
        task = next(
            task
            for task in runner.TASKS
            if task.task_id == "control_shallow_algebra"
        )
        self.assertIsNotNone(
            runner.validate_task_completion(
                task, "theorem a_different_name : True := by trivial\n"
            )
        )

    def test_completion_must_be_exactly_one_tagged_block(self) -> None:
        self.assertEqual(
            runner.extract_completion("<lean>\ntheorem x : True := by trivial\n</lean>"),
            "theorem x : True := by trivial\n",
        )
        for response in (
            "prose\n<lean>theorem x : True := by trivial</lean>",
            "<lean>theorem x : True := by trivial</lean>\nprose",
            "<lean>x</lean><lean>y</lean>",
        ):
            with self.subTest(response=response):
                with self.assertRaises(ValueError):
                    runner.extract_completion(response)

    def test_axiom_report_requires_full_unique_stdout(self) -> None:
        task = next(
            task
            for task in runner.TASKS
            if task.task_id == "control_shallow_algebra"
        )
        report = (
            "'Control.benchmark_check_control' depends on axioms: "
            "[propext, Classical.choice]"
        )
        self.assertEqual(
            runner.reported_axioms(task, report),
            {"propext", "Classical.choice"},
        )
        self.assertIsNone(runner.reported_axioms(task, f"forged\n{report}"))
        self.assertIsNone(runner.reported_axioms(task, f"{report}\n{report}"))

    def test_key_free_environment_removes_only_key_values(self) -> None:
        name = "LEANSLOP_TEST_API_KEY"
        previous = os.environ.get(name)
        os.environ[name] = "must-not-survive"
        try:
            environment, removed = runner.key_free_environment()
        finally:
            if previous is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = previous
        self.assertNotIn(name, environment)
        self.assertIn(name, removed)

    def test_compiler_environment_removes_common_secret_variables(self) -> None:
        names = ("LEANSLOP_TEST_TOKEN", "LEANSLOP_TEST_ACCESS_KEY")
        previous = {name: os.environ.get(name) for name in names}
        for name in names:
            os.environ[name] = "must-not-survive"
        try:
            environment, removed = runner.compiler_environment()
        finally:
            for name, value in previous.items():
                if value is None:
                    os.environ.pop(name, None)
                else:
                    os.environ[name] = value
        for name in names:
            self.assertNotIn(name, environment)
            self.assertIn(name, removed)

    def test_compiler_timeout_is_an_infrastructure_error(self) -> None:
        task = next(
            task
            for task in runner.TASKS
            if task.task_id == "control_shallow_algebra"
        )
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / "candidate.lean"
            source.write_text("", encoding="utf-8")
            cases = ((b"partial stdout", None), (None, b"partial stderr"))
            for stdout, stderr in cases:
                with self.subTest(stdout=stdout, stderr=stderr):
                    timeout = subprocess.TimeoutExpired(
                        ["lake"],
                        runner.COMPILER_TIMEOUT_SECONDS,
                        output=stdout,
                        stderr=stderr,
                    )
                    with patch.object(runner.subprocess, "run", side_effect=timeout):
                        with self.assertRaisesRegex(
                            runner.CompilerTimeoutError, "partial"
                        ):
                            runner.compile_source(task, source)

    def test_tool_router_stderr_is_detected(self) -> None:
        self.assertTrue(
            runner.TOOL_STDERR.search(
                "ERROR codex_core::tools::router: patch rejected: empty patch"
            )
        )


if __name__ == "__main__":
    unittest.main()
