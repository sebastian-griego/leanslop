# Dependency-redaction spot check

This benchmark tests the concrete Hahn-Banach proposal from the X thread
analyzed in this repository. It uses the real-valued sublinear form of
Hahn-Banach in mathlib and progressively moves the available frontier down its
canonical local proof path:

0. a shallow real-algebra control task
1. `riesz_extension`
2. `RieszExtension.exists_top`
3. `RieszExtension.step`
4. the complete local Riesz/Hahn-Banach scaffold

Each Hahn-Banach task imports only the three modules imported by mathlib's
`Analysis.Convex.Cone.Extension` module. A frontier declaration is represented
by a task-specific axiom at the shallower depths. The model receives the final
Hahn-Banach statement and the frontier statement, but no prescribed
intermediate lemma names or signatures.

These tiers are a controlled path ablation, not a complete theorem-DAG
redaction. A full experiment would compute each dependency closure, account for
alternate declarations, and sample every depth enough to estimate pass@k.

The runner sends only the task template and compiler diagnostics to the model.
It provides no tools and no access to the local mathlib source. Explicit
`sorry`, `admit`, `axiom`, `opaque`, or `unsafe` tokens are rejected before
compilation. A compiled wrapper enforces the complete required theorem type,
and its `#print axioms` output rejects any other injected axiom outside a small
allowlist of Lean's trusted core axioms plus the task's supplied frontier.
Any prohibited tool event terminates that trial so information from it cannot
enter a later repair attempt.

## Run

Sign in to Codex with a ChatGPT account, install the pinned Lean/mathlib
dependencies, and run:

```text
lake update
lake exe cache get
python benchmark/run_benchmark.py --model gpt-5.4
```

The runner removes all environment variables ending in `_API_KEY` and refuses
to start unless `codex login status` reports `Logged in using ChatGPT`. It
therefore uses the Codex CLI's existing ChatGPT session, not API-key
authentication.

Results are written below `benchmark/results/`. This is a spot check, not a
statistically powered benchmark: one repair trajectory cannot estimate pass@k,
measure a depth curve, or establish a claim about all current models.

The exact generated Lean candidates from the reported run are curated under
`benchmark/evidence/`. Run `python benchmark/verify_evidence.py` to recheck them
with the current type and axiom verifier.

Run `python benchmark/validate_templates.py` to adapt the canonical proof from
the pinned mathlib checkout and confirm that every template is satisfiable.
