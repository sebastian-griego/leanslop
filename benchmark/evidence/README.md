# Curated run evidence

This directory contains the exact assembled Lean sources from the reported
July 19, 2026 runs and the runner's original summary JSON files. The summaries
preserve model, authentication, token, timing, and repair-attempt metadata.
Raw Codex event streams are intentionally excluded because they include model
reasoning; the assembled sources preserve the code needed to audit proof
verification.

The historical runner checked compilation and `sorryAx`, but its required
signatures were comments rather than compiled assertions. The current runner
adds exact-type wrappers and checks the resulting axiom closure. Recheck the
unchanged generated completions under that hardened verifier with:

```text
python benchmark/verify_evidence.py
```

Expected result: the control passes, and all three sequential depth-1
Hahn-Banach attempts fail.
