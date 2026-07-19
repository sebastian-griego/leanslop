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
FORBIDDEN_META = re.compile(
    r"\b(native_decide|run_tac|by_elab|include_str|implemented_by|extern|"
    r"elab|elab_rules|syntax|macro|macro_rules|initialize|builtin_initialize|"
    r"set_option|attribute|unsafeCast|ofReduceBool|Lean|IO|System|dbg_trace|"
    r"trace_state|logInfo|guard_msgs)\b",
    flags=re.IGNORECASE,
)
FORBIDDEN_COMMAND = re.compile(
    r"^\s*(?:#|import\b|namespace\b|end\b|elab\b|syntax\b|macro\b|"
    r"initialize\b|builtin_initialize\b|set_option\b|attribute\b|section\b)",
    flags=re.MULTILINE,
)
TOOL_STDERR = re.compile(
    r"codex_core::tools::router|patch rejected:", flags=re.IGNORECASE
)
TRUSTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MODEL_TIMEOUT_SECONDS = 900
COMPILER_TIMEOUT_SECONDS = 180
SENSITIVE_COMPILER_ENV = re.compile(
    r"(?:API_KEY|TOKEN|SECRET|PASSWORD|PRIVATE_KEY|ACCESS_KEY|CREDENTIAL)",
    flags=re.IGNORECASE,
)


class CompilerTimeoutError(RuntimeError):
    """The verifier did not return a proof result within its infrastructure cap."""


@dataclass(frozen=True)
class Task:
    task_id: str
    depth: int
    frontier: str
    final_declaration: str
    verification_declaration: str
    supplied_axioms: tuple[str, ...] = ()
    family: str = "hahn_banach"

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
        family="control",
    ),
    Task(
        "baseline_hahn_banach_available",
        0,
        "The original mathlib Hahn-Banach theorem is imported and named",
        "BaselineHahnBanach.tested_hahn_banach",
        "BaselineHahnBanach.benchmark_check_hahn_banach",
    ),
    Task(
        "control_hahn_banach_premise_available",
        0,
        "A renamed Hahn-Banach theorem with the exact target signature is supplied",
        "ControlHahnBanach.tested_hahn_banach",
        "ControlHahnBanach.benchmark_check_hahn_banach",
        ("provided_hahn_banach",),
    ),
    Task(
        "rank_nullity_target_redacted",
        1,
        "Quotient dimensions and the kernel-range equivalence remain available",
        "RankNullity.tested_rank_nullity",
        "RankNullity.benchmark_check_rank_nullity",
        family="rank_nullity",
    ),
    Task(
        "intermediate_value_interfaces_redacted",
        2,
        "Connectedness and closed-order primitives remain; local IVT interfaces are absent",
        "IntermediateValue.tested_intermediate_value",
        "IntermediateValue.benchmark_check_intermediate_value",
        family="intermediate_value",
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
Work only from the shown imports, any supplied frontier declaration, and
compiler feedback. Do not assume that declarations from an omitted source
module remain available.
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


def compiler_environment() -> tuple[dict[str, str], list[str]]:
    environment = os.environ.copy()
    removed = sorted(name for name in environment if SENSITIVE_COMPILER_ENV.search(name))
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


def repository_status() -> str:
    process = subprocess.run(
        ["git", "status", "--short"],
        cwd=ROOT,
        text=True,
        encoding="utf-8",
        errors="replace",
        capture_output=True,
        timeout=30,
        check=False,
    )
    return process.stdout.strip() if process.returncode == 0 else "unavailable"


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
        timeout=MODEL_TIMEOUT_SECONDS,
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
        if event.get("type") in {"item.started", "item.completed", "item.failed"}:
            item = event.get("item", {})
            if item.get("type") == "agent_message":
                if event.get("type") == "item.completed":
                    text_parts.append(item.get("text", ""))
            elif item.get("type") not in {"reasoning", "todo_list"}:
                tool_events.append(
                    {"event_type": event.get("type"), "item": item}
                )
        elif event.get("type") == "turn.completed":
            usage = event.get("usage", {})

    tool_stderr_markers = TOOL_STDERR.findall(process.stderr)
    raw = {
        "command_model": model,
        "returncode": process.returncode,
        "events": events,
        "stderr": process.stderr,
        "unparsed_stdout_lines": parse_errors,
        "tool_events": tool_events,
        "tool_stderr_markers": tool_stderr_markers,
        "api_key_variables_removed": removed_key_variables,
    }
    if process.returncode != 0:
        raise RuntimeError(
            "Codex CLI failed with exit code "
            f"{process.returncode}: {(process.stderr or process.stdout)[-4000:]}"
        )
    return "\n".join(text_parts), usage, raw


def extract_completion(text: str) -> str:
    if text.count("<lean>") != 1 or text.count("</lean>") != 1:
        raise ValueError("response was not exactly one <lean>...</lean> block")
    match = re.fullmatch(r"\s*<lean>\s*(.*?)\s*</lean>\s*", text, flags=re.DOTALL)
    if not match:
        raise ValueError("response was not exactly one <lean>...</lean> block")
    return match.group(1).strip() + "\n"


def validate_completion(completion: str) -> str | None:
    match = FORBIDDEN.search(completion)
    if match:
        return f"completion contains forbidden token: {match.group(1)}"
    if match := FORBIDDEN_META.search(completion):
        return f"completion contains forbidden meta or I/O token: {match.group(1)}"
    if FORBIDDEN_COMMAND.search(completion):
        return "completion contains a forbidden command or changes fixed structure"
    return None


def validate_task_completion(task: Task, completion: str) -> str | None:
    if validation_error := validate_completion(completion):
        return validation_error
    short_name = task.final_declaration.rsplit(".", 1)[-1]
    declaration = re.compile(
        rf"^\s*(?:(?:private|protected)\s+)?"
        rf"(?:theorem|lemma|def|abbrev)\s+{re.escape(short_name)}"
        rf"(?=\s|\(|\[|\{{|:)",
        flags=re.MULTILINE,
    )
    if len(declaration.findall(completion)) != 1:
        return f"completion must declare `{short_name}` exactly once"
    verification_name = task.verification_declaration.rsplit(".", 1)[-1]
    if re.search(rf"\b{re.escape(verification_name)}\b", completion):
        return "completion attempts to shadow or reference the fixed verifier"
    return None


def reported_axioms(task: Task, stdout: str) -> set[str] | None:
    report_pattern = re.compile(
        rf"\s*'{re.escape(task.verification_declaration)}' "
        rf"(?:(?:depends on axioms: \[(?P<axioms>[^\]]*)\])|"
        rf"(?:does not depend on any axioms))\s*",
        flags=re.DOTALL,
    )
    match = report_pattern.fullmatch(stdout)
    if not match:
        return None
    if match.group("axioms") is None:
        return set()
    return {
        name.strip()
        for name in match.group("axioms").split(",")
        if name.strip()
    }


def compile_source(task: Task, source_path: Path) -> tuple[bool, str, float]:
    started = time.monotonic()
    try:
        environment, _ = compiler_environment()
        process = subprocess.run(
            ["lake", "env", "lean", str(source_path)],
            cwd=ROOT,
            text=True,
            encoding="utf-8",
            errors="replace",
            capture_output=True,
            timeout=COMPILER_TIMEOUT_SECONDS,
            check=False,
            env=environment,
        )
        output = (process.stdout + process.stderr).strip()
        passed = process.returncode == 0
        if passed:
            if process.stderr.strip():
                passed = False
                output += "\nRejected: successful compilation produced stderr output."
            axioms = reported_axioms(task, process.stdout) if passed else None
            allowed_axioms = TRUSTED_AXIOMS | set(task.supplied_axioms)
            if passed and axioms is None:
                passed = False
                output += (
                    "\nRejected: stdout was not exactly one final axiom report."
                )
            elif passed and (unexpected := axioms - allowed_axioms):
                passed = False
                output += (
                    "\nRejected: final declaration depends on unexpected axioms: "
                    + ", ".join(sorted(unexpected))
                )
        return passed, output, time.monotonic() - started
    except subprocess.TimeoutExpired as error:
        def timeout_text(value: str | bytes | None) -> str:
            if isinstance(value, bytes):
                return value.decode("utf-8", errors="replace")
            return value or ""

        output = (timeout_text(error.stdout) + timeout_text(error.stderr)).strip()
        raise CompilerTimeoutError(
            f"{output}\nCompilation timed out after "
            f"{COMPILER_TIMEOUT_SECONDS} seconds."
        )


def initial_prompt(task: Task, template: str) -> str:
    return f"""\
Task: {task.task_id}
Benchmark family: {task.family}
Family-specific redaction tier: {task.depth}
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
            transcript_sha256 = hashlib.sha256(
                render_transcript(messages).encode("utf-8")
            ).hexdigest()
            model_started = time.monotonic()
            text, usage, raw_response = codex_message(model, messages, isolated_dir)
            model_seconds = time.monotonic() - model_started
            token_totals["input_tokens"] += int(usage.get("input_tokens", 0))
            token_totals["output_tokens"] += int(usage.get("output_tokens", 0))

            raw_response_bytes = (
                json.dumps(raw_response, indent=2, ensure_ascii=False) + "\n"
            ).encode("utf-8")
            (trial_dir / f"attempt_{attempt_number}_response.json").write_bytes(
                raw_response_bytes
            )

            tool_attempts = list(raw_response["tool_events"]) + [
                {"event_type": "stderr", "marker": marker}
                for marker in raw_response["tool_stderr_markers"]
            ]
            protocol_errors = raw_response["unparsed_stdout_lines"]
            stop_after_attempt = bool(tool_attempts or protocol_errors)
            if tool_attempts:
                completion = ""
                validation_error = (
                    "Codex attempted prohibited tool activity: "
                    + json.dumps(tool_attempts, ensure_ascii=False)
                )
            elif protocol_errors:
                completion = ""
                validation_error = (
                    "Codex emitted unparsed protocol output: "
                    + json.dumps(protocol_errors, ensure_ascii=False)
                )
            else:
                try:
                    completion = extract_completion(text)
                    validation_error = validate_task_completion(task, completion)
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

            diagnostic_bytes = (compiler_output + "\n").encode("utf-8")
            (trial_dir / f"attempt_{attempt_number}_diagnostic.txt").write_bytes(
                diagnostic_bytes
            )
            attempts.append(
                {
                    "attempt": attempt_number,
                    "model_seconds": round(model_seconds, 3),
                    "compile_seconds": round(compile_seconds, 3),
                    "compiled": compiled,
                    "validation_error": validation_error,
                    "usage": usage,
                    "transcript_sha256": transcript_sha256,
                    "raw_response_sha256": hashlib.sha256(
                        raw_response_bytes
                    ).hexdigest(),
                    "completion_sha256": (
                        hashlib.sha256(completion.encode("utf-8")).hexdigest()
                        if completion
                        else None
                    ),
                    "source_sha256": (
                        file_sha256(source_path)
                        if not validation_error
                        else None
                    ),
                    "diagnostic_sha256": hashlib.sha256(
                        diagnostic_bytes
                    ).hexdigest(),
                    "tool_attempts": tool_attempts,
                }
            )
            if compiled:
                break
            if stop_after_attempt:
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
        "family": task.family,
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
    parser.add_argument("--model", default="gpt-5.6-sol")
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
    _, compiler_removed_variables = compiler_environment()
    selected = [task for task in TASKS if not args.task or task.task_id in args.task]
    key_free_env, _ = key_free_environment()
    started_at = datetime.now(timezone.utc)
    metadata = {
        "started_at": started_at.isoformat(),
        "model": args.model,
        "provider": "Codex CLI with ChatGPT authentication",
        "trials": args.trials,
        "max_attempts": args.max_attempts,
        "reasoning_effort": "high",
        "model_timeout_seconds": MODEL_TIMEOUT_SECONDS,
        "compiler_timeout_seconds": COMPILER_TIMEOUT_SECONDS,
        "api_keys": (
            "not used; *_API_KEY variables removed from Codex and Lean subprocesses"
        ),
        "api_key_variables_removed": removed_key_variables,
        "compiler_sensitive_variables_removed": compiler_removed_variables,
        "codex_cli_version": command_output(
            [codex_executable(), "--version"], key_free_env
        ),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "lean_version": command_output(["lake", "env", "lean", "--version"]),
        "mathlib": mathlib_metadata(),
        "benchmark_git_commit": repository_commit(),
        "benchmark_git_status": repository_status(),
        "runner_sha256": file_sha256(Path(__file__).resolve()),
        "validator_sha256": file_sha256(
            ROOT / "benchmark" / "validate_templates.py"
        ),
        "system_prompt_sha256": hashlib.sha256(
            SYSTEM_PROMPT.encode("utf-8")
        ).hexdigest(),
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
