# LeanSlop

An evidence-backed investigation of Doomslide's July 19, 2026 proposal to test
LLM theorem proving by progressively redacting intermediate mathlib
declarations.

The main result is a qualified one: `gpt-5.6-sol` showed an 8/8 to 0/14
one-shot cliff between direct Hahn-Banach theorem availability and redacted
Hahn-Banach frontiers, but a depth-1 proof succeeded after one Lean feedback
turn. This supports a serious dependency/interface bottleneck, not a categorical
inability claim or a measured depth-scaling law.

- [Research report](REPORT.md)
- [Benchmark design and usage](benchmark/README.md)
- [Curated, hash-verified evidence](benchmark/evidence/README.md)
- [Machine-readable result summary](benchmark/result-summary.json)

No API keys were used. Model generation ran through an authenticated ChatGPT
session in the Codex CLI, with `*_API_KEY` variables removed.

The project is pinned to Lean and mathlib `v4.32.0`.
