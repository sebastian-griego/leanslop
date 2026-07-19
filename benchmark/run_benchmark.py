#!/usr/bin/env python3
"""Run premise-redacted Lean tasks through an authenticated Codex session."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TASK_DIR = ROOT / "benchmark" / "tasks"
RESULTS_DIR = ROOT / "benchmark" / "results"
MARKER = "__MODEL_COMPLETION__"
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|opaque|unsafe)\b", re.IGNORECASE)
TRUSTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


@dataclass(frozen=True)
class Task:
    task_id: str
    depth: int
    frontier: str
    final_declaration: str
    verification_declaration: str
    supplied_axioms: tuple[str, ...] = ()

    @property
    def path(self) -> Path:
        return TASK_DIR / f"{self.task_id}.lean.in"


TASKS = (
    Task(
        "control_shallow_algebra",
        0,
        "Standard real arithmetic and tactics",
        "Control.tested_shallow_control",
        "Control.benchmark_check_control",
    ),
    Task(
        "depth1_riesz_available",
        1,
        "A supplied M. Riesz extension theorem",
        "Depth1.tested_hahn_banach",
        "Depth1.benchmark_check_hahn_banach",
        ("provided_riesz_extension",),
    ),
    Task(
        "depth2_maximal_extension_available",
        2,
        "A supplied maximal partial extension theorem",
        "Depth2.tested_hahn_banach",
        "Depth2.benchmark_check_hahn_banach",
        ("provided_exists_top",),
    ),
    Task(
        "depth3_one_step_available",
        3,
        "A supplied one-dimensional extension step",
        "Depth3.tested_hahn_banach",
        "Depth3.benchmark_check_hahn_banach",
        ("provided_step",),
    ),
    Task(
        "depth4_no_scaffold",
        4,
        "Only the foundational imports; no Riesz/Hahn-Banach result",
        "Depth4.tested_hahn_banach",
        "Depth4.benchmark_check_hahn_banach",
    ),
)


SYSTEM_PROMPT = """\
You are completing a controlled Lean 4 theorem-proving benchmark.
Return only Lean code between <lean> and </lean> tags.

The code replaces one marker inside a fixed file. Do not emit imports, namespace
commands, `end`, markdown fences, prose, or changes to supplied declarations.
You may define helper lemmas and the required theorems. You must not use
`sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or any equivalent escape hatch.
The original Mathlib.Analysis.Convex.Cone.Extension module is deliberately not
imported, so its Riesz and Hahn-Banach declarations are unavailable. Work only
from the shown imports, supplied frontier axiom (if any), and compiler feedback.
"""


def codex_executable() -> str:
    executable = shutil.which("codex.cmd" if os.name == "nt" else "codex")
    if not executable:
        raise RuntimeError("Codex CLI executable was not found on PATH")
    return executable


def key_free_environment() -> tuple[dict[str, str], list[str]]:
    environment = os.environ.copy()
    removed = sorted(
        name for name in environment if name.upper().endswith("_API_KEY")
    )
    for name in removed:
        environment.pop(name, None)
    return environment, removed


def require_chatgpt_authentication() -> list[str]:
    environment, removed = key_free_environment()
    process = subprocess.run(
        [codex_executable(), "login", "status"],
        text=True,
        encoding="utf-8",
        errors="replace",
        capture_output=True,
        timeout=30,
        check=False,
        env=environment,
    )
    output = (process.stdout + process.stderr).strip()
    if process.returncode != 0 or "Logged in using ChatGPT" not in output:
        raise RuntimeError(
            "The benchmark requires `codex login` with a ChatGPT account; "
            "API-key authentication is not allowed."
        )
    return removed


def command_output(command: list[str], environment: dict[str, str] | None = None) -> str:
    process = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        encoding="utf-8",
        errors="replace",
        capture_output=True,
        timeout=30,
        check=False,
        env=environment,
    )
    if process.returncode != 0:
        raise RuntimeError(
            f"`{' '.join(command)}` failed: {(process.stderr or process.stdout).strip()}"
        )
    return (process.stdout + process.stderr).strip()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def repository_commit() -> str | None:
    process = subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD"],
        cwd=ROOT,
        text=True,
        encoding="utf-8",
        errors="replace",
        capture_output=True,
        timeout=30,
        check=False,
    )
    return process.stdout.strip() if process.returncode == 0 else None


def mathlib_metadata() -> dict[str, str]:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    package = next(
        package for package in manifest["packages"] if package["name"] == "mathlib"
    )
    installed_commit = command_output(
        ["git", "-C", str(ROOT / ".lake" / "packages" / "mathlib"), "rev-parse", "HEAD"]
    )
    if installed_commit != package["rev"]:
        raise RuntimeError(
            "The installed mathlib checkout does not match lake-manifest.json: "
            f"{installed_commit} != {package['rev']}"
        )
    return {
        "input_revision": package["inputRev"],
        "manifest_commit": package["rev"],
        "installed_commit": installed_commit,
    }


def render_transcript(messages: list[dict[str, str]]) -> str:
    turns = [SYSTEM_PROMPT]
    for message in messages:
        turns.append(f"\n<{message['role']}>\n{message['content']}\n</{message['role']}>")
    return "\n".join(turns)


def codex_message(
    model: str, messages: list[dict[str, str]], isolated_dir: Path
) -> tuple[str, dict, dict]:
    command = [
        codex_executable(),
        "exec",
        "-C",
        str(isolated_dir),
        "--skip-git-repo-check",
        "--ephemeral",
        "--ignore-user-config",
        "--ignore-rules",
        "-s",
        "read-only",
        "-m",
        model,
        "-c",
        'model_reasoning_effort="high"',
        "-c",
        'web_search="disabled"',
        "--disable",
        "shell_tool",
        "--disable",
        "browser_use",
        "--disable",
        "browser_use_external",
        "--disable",
        "browser_use_full_cdp_access",
        "--disable",
        "computer_use",
        "--disable",
        "apps",
        "--disable",
        "code_mode_host",
        "--disable",
        "tool_suggest",
        "--disable",
        "goals",
        "--json",
        "-",
    ]
    environment, removed_key_variables = key_free_environment()

    process = subprocess.run(
        command,
        cwd=isolated_dir,
        input=render_transcript(messages),
        text=True,
        encoding="utf-8",
        errors="replace",
        capture_output=True,
        timeout=900,
        check=False,
        env=environment,
    )
    events = []
    parse_errors = []
    for line in process.stdout.splitlines():
        if not line.strip():
            continue
        try:
            events.append(json.loads(line))
        except json.JSONDecodeError:
            parse_errors.append(line)

    text_parts = []
    tool_events = []
    usage = {}
    for event in events:
        if event.get("type") == "item.completed":
            item = event.get("item", {})
            if item.get("type") == "agent_message":
                text_parts.append(item.get("text", ""))
            elif item.get("type") not in {"reasoning", "todo_list"}:
                tool_events.append(item)
        elif event.get("type") == "turn.completed":
            usage = event.get("usage", {})

    raw = {
        "command_model": model,
        "returncode": process.returncode,
        "events": events,
        "stderr": process.stderr,
        "unparsed_stdout_lines": parse_errors,
        "tool_events": tool_events,
        "api_key_variables_removed": removed_key_variables,
    }
    if process.returncode != 0:
        raise RuntimeError(
            "Codex CLI failed with exit code "
            f"{process.returncode}: {(process.stderr or process.stdout)[-4000:]}"
        )
    return "\n".join(text_parts), usage, raw


def extract_completion(text: str) -> str:
    match = re.search(r"<lean>\s*(.*?)\s*</lean>", text, flags=re.DOTALL)
    if not match:
        raise ValueError("response did not contain <lean>...</lean>")
    return match.group(1).strip() + "\n"


def validate_completion(completion: str) -> str | None:
    match = FORBIDDEN.search(completion)
    if match:
        return f"completion contains forbidden token: {match.group(1)}"
    if re.search(r"^\s*(import|namespace|end)\b", completion, flags=re.MULTILINE):
        return "completion changes the fixed import or namespace structure"
    return None


def reported_axioms(task: Task, output: str) -> set[str] | None:
    pattern = re.compile(
        rf"'{re.escape(task.verification_declaration)}' depends on axioms: \[(.*?)\]",
        flags=re.DOTALL,
    )
    match = pattern.search(output)
    if match:
        return {name.strip() for name in match.group(1).split(",") if name.strip()}
    if f"'{task.verification_declaration}' does not depend on any axioms" in output:
        return set()
    return None


def compile_source(task: Task, source_path: Path) -> tuple[bool, str, float]:
    started = time.monotonic()
    try:
        process = subprocess.run(
            ["lake", "env", "lean", str(source_path)],
            cwd=ROOT,
            text=True,
            encoding="utf-8",
            errors="replace",
            capture_output=True,
            timeout=180,
            check=False,
        )
        output = (process.stdout + process.stderr).strip()
        passed = process.returncode == 0
        if passed:
            axioms = reported_axioms(task, output)
            allowed_axioms = TRUSTED_AXIOMS | set(task.supplied_axioms)
            if axioms is None:
                passed = False
                output += "\nRejected: verifier could not read the final axiom report."
            elif unexpected := axioms - allowed_axioms:
                passed = False
                output += (
                    "\nRejected: final declaration depends on unexpected axioms: "
                    + ", ".join(sorted(unexpected))
                )
        return passed, output, time.monotonic() - started
    except subprocess.TimeoutExpired as error:
        output = ((error.stdout or "") + (error.stderr or "")).strip()
        elapsed = time.monotonic() - started
        return False, f"{output}\nCompilation timed out after 180 seconds.", elapsed


def initial_prompt(task: Task, template: str) -> str:
    return f"""\
Task: {task.task_id}
Redaction depth: {task.depth}
Available frontier: {task.frontier}

Replace the literal marker `{MARKER}` with declarations that satisfy every
`REQUIRED` signature in the fixed template. The final declaration is
`{task.final_declaration}`. Keep the supplied axiom, imports, options,
statements, and namespace unchanged.

Fixed template:

<template>
{template}
</template>
"""


def repair_prompt(completion: str, diagnostic: str) -> str:
    return f"""\
The proposed replacement did not pass the verifier.

Replacement:
<lean>
{completion}
</lean>

Verifier diagnostic:
<diagnostic>
{diagnostic[-16000:]}
</diagnostic>

Return a corrected complete replacement for `{MARKER}`. Follow the original
constraints and emit only <lean>...</lean>.
"""


def run_trial(
    task: Task,
    trial: int,
    model: str,
    max_attempts: int,
    run_dir: Path,
) -> dict:
    template = task.path.read_text(encoding="utf-8")
    if template.count(MARKER) != 1:
        raise RuntimeError(f"{task.path} must contain exactly one {MARKER}")

    trial_dir = run_dir / task.task_id / f"trial_{trial}"
    trial_dir.mkdir(parents=True, exist_ok=True)
    messages: list[dict[str, str]] = [
        {"role": "user", "content": initial_prompt(task, template)}
    ]
    attempts: list[dict] = []
    token_totals = {"input_tokens": 0, "output_tokens": 0}

    with tempfile.TemporaryDirectory(prefix="leanslop_codex_") as isolated:
        isolated_dir = Path(isolated)
        for attempt_number in range(1, max_attempts + 1):
            model_started = time.monotonic()
            text, usage, raw_response = codex_message(model, messages, isolated_dir)
            model_seconds = time.monotonic() - model_started
            token_totals["input_tokens"] += int(usage.get("input_tokens", 0))
            token_totals["output_tokens"] += int(usage.get("output_tokens", 0))

            (trial_dir / f"attempt_{attempt_number}_response.json").write_text(
                json.dumps(raw_response, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )

            if raw_response["tool_events"]:
                completion = ""
                validation_error = (
                    "Codex used prohibited tools: "
                    + ", ".join(
                        str(item.get("type")) for item in raw_response["tool_events"]
                    )
                )
            else:
                try:
                    completion = extract_completion(text)
                    validation_error = validate_completion(completion)
                except ValueError as error:
                    completion = ""
                    validation_error = str(error)

            if validation_error:
                compiled = False
                compiler_output = validation_error
                compile_seconds = 0.0
            else:
                source = template.replace(MARKER, completion)
                source_path = trial_dir / f"attempt_{attempt_number}.lean"
                source_path.write_text(source, encoding="utf-8")
                compiled, compiler_output, compile_seconds = compile_source(task, source_path)

            (trial_dir / f"attempt_{attempt_number}_diagnostic.txt").write_text(
                compiler_output + "\n",
                encoding="utf-8",
            )
            attempts.append(
                {
                    "attempt": attempt_number,
                    "model_seconds": round(model_seconds, 3),
                    "compile_seconds": round(compile_seconds, 3),
                    "compiled": compiled,
                    "validation_error": validation_error,
                    "usage": usage,
                }
            )
            if compiled:
                break
            if raw_response["tool_events"]:
                break

            messages.extend(
                [
                    {"role": "assistant", "content": text},
                    {
                        "role": "user",
                        "content": repair_prompt(completion, compiler_output),
                    },
                ]
            )

    result = {
        "task_id": task.task_id,
        "depth": task.depth,
        "frontier": task.frontier,
        "final_declaration": task.final_declaration,
        "verification_declaration": task.verification_declaration,
        "trial": trial,
        "model": model,
        "passed": bool(attempts and attempts[-1]["compiled"]),
        "attempts_used": len(attempts),
        "token_totals": token_totals,
        "attempts": attempts,
    }
    (trial_dir / "result.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    return result


def positive_integer(value: str) -> int:
    parsed = int(value)
    if parsed < 1:
        raise argparse.ArgumentTypeError("must be at least 1")
    return parsed


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", default="gpt-5.4")
    parser.add_argument("--trials", type=positive_integer, default=1)
    parser.add_argument("--max-attempts", type=positive_integer, default=3)
    parser.add_argument(
        "--task",
        action="append",
        choices=[task.task_id for task in TASKS],
        help="Run only the named task; repeat to select multiple tasks.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    removed_key_variables = require_chatgpt_authentication()
    selected = [task for task in TASKS if not args.task or task.task_id in args.task]
    key_free_env, _ = key_free_environment()
    started_at = datetime.now(timezone.utc)
    metadata = {
        "started_at": started_at.isoformat(),
        "model": args.model,
        "provider": "Codex CLI with ChatGPT authentication",
        "trials": args.trials,
        "max_attempts": args.max_attempts,
        "api_keys": "not used; *_API_KEY variables removed from Codex subprocesses",
        "api_key_variables_removed": removed_key_variables,
        "codex_cli_version": command_output(
            [codex_executable(), "--version"], key_free_env
        ),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "lean_version": command_output(["lake", "env", "lean", "--version"]),
        "mathlib": mathlib_metadata(),
        "benchmark_git_commit": repository_commit(),
        "runner_sha256": file_sha256(Path(__file__).resolve()),
        "task_sha256": {task.task_id: file_sha256(task.path) for task in selected},
        "tasks": [task.task_id for task in selected],
    }
    run_dir = RESULTS_DIR / started_at.strftime("%Y%m%dT%H%M%SZ")
    run_dir.mkdir(parents=True, exist_ok=False)
    (run_dir / "metadata.json").write_text(
        json.dumps(metadata, indent=2) + "\n", encoding="utf-8"
    )

    results = []
    infrastructure_failures = []
    for task in selected:
        for trial in range(1, args.trials + 1):
            print(f"[{task.task_id}] trial {trial}", flush=True)
            try:
                result = run_trial(
                    task,
                    trial,
                    args.model,
                    args.max_attempts,
                    run_dir,
                )
            except (RuntimeError, subprocess.TimeoutExpired) as error:
                failure = {
                    "task_id": task.task_id,
                    "trial": trial,
                    "error_type": type(error).__name__,
                    "error": str(error),
                }
                infrastructure_failures.append(failure)
                print(f"  INFRASTRUCTURE ERROR: {error}", flush=True)
                continue
            results.append(result)
            print(
                f"  {'PASS' if result['passed'] else 'FAIL'} "
                f"after {result['attempts_used']} attempt(s)",
                flush=True,
            )

    summary = {
        **metadata,
        "finished_at": datetime.now(timezone.utc).isoformat(),
        "status": "infrastructure_error" if infrastructure_failures else "completed",
        "results": results,
        "infrastructure_failures": infrastructure_failures,
        "passed": sum(result["passed"] for result in results),
        "total_completed": len(results),
        "total_requested": len(selected) * args.trials,
    }
    (run_dir / "summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"Summary: {summary['passed']}/{summary['total_completed']} passed")
    print(run_dir.relative_to(ROOT))
    if infrastructure_failures:
        return 2
    return 0 if summary["passed"] == summary["total_completed"] else 1


if __name__ == "__main__":
    sys.exit(main())
