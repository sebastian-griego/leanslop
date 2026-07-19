# LeanSlop

An evidence-backed investigation of LLM theorem proving under progressive
redaction of intermediate mathlib declarations.

The main result is a qualified one: `gpt-5.6-sol` showed an 8/8 to 0/14
one-shot cliff between direct Hahn-Banach theorem availability and redacted
Hahn-Banach frontiers, but a depth-1 proof succeeded after one Lean feedback
turn. This supports an observed dependency/interface bottleneck, not a
categorical inability claim or a measured depth-scaling law.

- [Research report](REPORT.md)
- [Benchmark design and usage](benchmark/README.md)
- [Curated, hash-verified evidence](benchmark/evidence/README.md)
- [Machine-readable result summary](benchmark/result-summary.json)

The project is pinned to Lean and mathlib `v4.32.0`.
