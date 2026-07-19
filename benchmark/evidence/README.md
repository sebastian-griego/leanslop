# Curated run evidence

Two evidence sets are committed:

- `2026-07-19/` preserves the original `gpt-5.4` shallow-control and adaptive
  depth-1 spot check.
- `2026-07-19-expanded/` contains the completed `gpt-5.6-sol` one-shot matrix,
  matched controls, adaptive depth-1 through depth-4 runs, and the small
  `gpt-5.5` comparison.

The expanded set contains:

- 13 completed run directories;
- 37 trial records and 44 generated Lean attempts;
- assembled `.lean` sources and compiler diagnostics;
- per-trial results plus run metadata and summaries;
- a manifest with SHA-256 and byte length for every included file.

Raw `attempt_*_response.json` files are intentionally excluded because they
contain model reasoning. The manifest asserts this exclusion, and the verifier
rejects any such file in the curated tree.

The manifest also records:

- a disposition for every local result directory, including four incomplete
  launchers, two startup artifacts, two superseded pilots, and the two runs
  preserved in the legacy evidence set;
- the exact successful baseline trial whose stderr reported a rejected empty
  patch attempt;
- model, task, attempt, timing, token, and generation-configuration metadata
  inherited from each run.

Run:

```text
python benchmark/verify_evidence.py
```

The verifier checks the manifest file set and hashes, extracts every completion
against the current task template, applies the hardened static policy, recompiles
all attempts, and compares each result with its recorded status. It then checks
the final declaration's exact type and axiom closure.
