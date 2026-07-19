# Dependency-redaction benchmark

This benchmark tests the concrete Hahn-Banach proposal analyzed in
[`REPORT.md`](../REPORT.md): hide a theorem and successively earlier
intermediate declarations, then ask a model to reconstruct the missing Lean
development.

## Task families

The Hahn-Banach series uses the real-valued sublinear theorem in mathlib:

```text
exists_extension_of_le_sublinear
  -> riesz_extension
    -> RieszExtension.exists_top
      -> RieszExtension.step
```

Depths 1 through 4 supply progressively earlier frontiers along that path. A
matched control supplies a renamed theorem with the exact final signature under
the same narrow imports; a separate library sanity baseline imports the original
extension module. Rank-nullity and intermediate-value tasks test different
redaction patterns.

The tiers are canonical-path ablations, not complete theorem-DAG layers.
Family-local numeric labels are not comparable across task families.

## Verification boundary

The runner:

- requires `codex login status` to report ChatGPT authentication;
- removes every `*_API_KEY` environment variable from Codex and scrubs common
  key, token, secret, password, and credential variables from Lean;
- invokes Codex in a fresh ephemeral directory with shell, browser, web, app,
  code-host, and related tools disabled;
- rejects recorded or stderr-reported tool attempts;
- statically rejects proof bypasses, command-level metaprogramming, and
  compile-time I/O;
- compiles an exact target-type wrapper with pinned Lean/mathlib;
- accepts exactly one stdout axiom report and rejects unexpected axioms.

This uses a ChatGPT subscription session, not API-key authentication. The Lean
compiler is hardened by environment scrubbing and static screening but is not
inside an OS-level filesystem sandbox. Treat arbitrary model completions as
untrusted code outside this controlled task set.

## Validate templates

Install the pinned dependencies and prove that the hidden declarations are
absent while canonical reference reconstructions still compile:

```text
lake update
lake exe cache get
python benchmark/validate_templates.py
```

## Run

A single matched-control trial:

```text
python benchmark/run_benchmark.py \
  --model gpt-5.6-sol \
  --trials 1 \
  --max-attempts 1 \
  --task control_hahn_banach_premise_available
```

A one-shot Hahn-Banach matrix:

```text
python benchmark/run_benchmark.py --model gpt-5.6-sol --trials 1 --max-attempts 1 --task control_hahn_banach_premise_available --task depth1_riesz_available --task depth2_maximal_extension_available --task depth3_one_step_available --task depth4_no_scaffold
```

Omitting `--task` runs every task. Output is written below
`benchmark/results/`, which is ignored by Git because raw response JSON includes
model reasoning.

One-shot trials are independent samples. Setting `--max-attempts` above one
creates an adaptive conversation in which later attempts receive the preceding
Lean diagnostic; those attempts must not be reported as independent pass@k
samples.

## Evidence

The reported runs are curated under [`benchmark/evidence`](evidence/README.md).
Only assembled Lean, diagnostics, result/summary metadata, and hashes are
committed. Raw response streams are excluded.

Recheck the evidence with the current static policy, compiler, exact type, and
axiom verifier:

```text
python -m unittest benchmark/test_harness.py
python benchmark/verify_evidence.py
```

`curate_evidence.py` enforces the report's exact included/excluded run registry,
cross-checks summaries and stored artifact hashes, and refuses to include raw
response artifacts.
