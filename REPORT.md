# Dependency redaction as a test of LLM proof reconstruction

## Verdict

The experiment gives **qualified support** to a dependency-interface
bottleneck, but not to a categorical inability claim.

- With `gpt-5.6-sol`, a named or renamed Hahn-Banach result was used
  successfully in 8/8 one-shot controls.
- The same model produced 0/14 verified one-shot proofs after the final
  Hahn-Banach theorem was removed, across four canonical-path frontiers.
- The all-zero redacted tiers show a **cliff**, not the proposed scaling curve.
  There is no measured slope among depths 1 through 4.
- In a separate adaptive run, depth 1 verified on attempt 2 after one Lean
  diagnostic. Depths 2, 3, and 4 remained unverified after three attempts.
- Redaction was not universally fatal: the model solved rank-nullity in 3/3
  one-shot trials and an intermediate-value theorem in 1/3.

The supported conclusion is narrow: **removing familiar intermediate
interfaces sharply reduced one-shot reliability on this Hahn-Banach target.**
The tests do not show that current LLMs are categorically unable to reconstruct
such mathematics, and they do not establish monotonic performance scaling with
dependency depth.

## What the proposal says

The [initial proposal](https://x.com/i/status/2078858292709728700) claims that
current LLMs cannot construct some undergraduate parts of mathlib. The
surrounding discussion makes the test more precise:

1. The claim is based on informal checks rather than a published experiment.
2. The task is to prove a theorem with
   [no intermediate lemmas available](https://x.com/i/status/2078859195491700903).
3. Hahn-Banach is offered as a concrete target.
4. The [specific experiment](https://x.com/i/status/2078869136017387781)
   removes declarations at several dependency-graph depths and observes how
   performance changes.

The proposed mechanism is that ordinary benchmarks favor shallow problems,
where a proof remains close to the stated goal, while longer arguments can
remain difficult even when each local step is simple. The discussion also
distinguishes broad counterexample search from depth-first proof construction.

The proposal does not specify a model, theorem sample, context policy, compute
budget, graph-redaction algorithm, or success metric. This report
operationalizes it as a fixed-budget, Lean-verified pass rate.

### Historical continuity and qualifications

Earlier versions of the idea considered reconstructing all or part of mathlib,
the inference cost of doing so, and the distinction between cached proofs and
compact programs that can generate them. The broader position is contingent
rather than an architectural impossibility claim: likely factors include the
scale of formal training data, the ability to gather useful context, and the
amount of inference-time search.

## Surrounding debate

The proposal arose amid recent reports of AI-assisted mathematical results and
broad predictions about near-term mathematical automation. One
[reported example](https://x.com/i/status/2077082912021786660) produced a
counterexample in false-discovery-rate theory after roughly 90 minutes.

That result is real evidence of mathematical capability, but it is also a
counterexample-search task rather than a long formal reconstruction. Compute
matters as well: performance under a large search budget is a different
question from fixed-budget one-shot reliability.

Two reply-chain counterexamples do not implement the proposed ablation:

- An [AI-assisted undergraduate formalization project](https://github.com/rkirov/linear-algebra-done-right-lean)
  is substantial, but it uses mathlib directly, receives roughly one to two
  hours of line-by-line human review per subsection, leaves exercises as
  `sorry`, and prose-defers some numbered results.
- Public assertions that existing systems can already complete the proposed
  task have not been accompanied by a controlled declaration-redaction result.

A reported
[number-theory result](https://x.com/i/status/2078732544070074777) is evidence
of informal AI-assisted mathematical discovery, not Lean formalization or
dependency reconstruction. The final account describes an AI-human
collaboration rather than an autonomous result.

## What a valid redaction test requires

Removing proof bodies is not enough. If proposition declarations remain
callable, the model can reuse them without reconstructing anything. A stronger
experiment should:

- remove declarations, not merely implementations;
- measure theorem-DAG distance rather than file-import distance;
- account for aliases and alternative routes whose closure reaches a hidden
  result;
- keep imports, model, prompt policy, feedback, sampling, and compute fixed;
- deny source retrieval during generation;
- compile exact target types and reject proof bypasses;
- report independent samples separately from adaptive repairs.

No paper found in this review implements the exact progressive
declaration-redaction experiment. The local benchmark is therefore a targeted
spot check rather than a replication of an established protocol.

## Benchmark design

Hahn-Banach says, roughly, that a linear rule defined on part of a vector space
can be extended to the whole space without violating its original bound. The
benchmark uses mathlib's algebraic real-valued form: a partial linear map
dominated by a sublinear function must have a total linear extension with the
same domination property.

This is not a test made by deleting arbitrary lines from a proof. Every task
asks for the same final theorem under controlled imports. The controls leave the
finished result available, either under its library name or as an exact renamed
premise. The redacted tasks remove that final declaration and expose
progressively earlier named checkpoints along one known proof path. The model
must reconstruct everything between the available checkpoint and the final
statement.

The pinned environment is Lean and mathlib `v4.32.0`, with mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`. The relevant canonical local path
in mathlib is:

```text
exists_extension_of_le_sublinear
  -> riesz_extension
    -> RieszExtension.exists_top
      -> RieszExtension.step
```

The source is mathlib's
[cone-extension module](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Convex/Cone/Extension.lean).
The normed-space
[Hahn-Banach wrapper](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Normed/Module/HahnBanach.lean)
builds on this algebraic real-valued result.

| Class | Available frontier | Purpose |
|---|---|---|
| Matched control | Renamed theorem with the exact target type | Same narrow imports and interface as redacted tasks |
| Library sanity baseline | Original extension module and named final theorem | Confirms ordinary theorem lookup |
| Hahn depth 1 | Supplied `riesz_extension` equivalent | Reconstruct final reduction |
| Hahn depth 2 | Supplied `RieszExtension.exists_top` equivalent | Reconstruct Riesz and final reduction |
| Hahn depth 3 | Supplied `RieszExtension.step` equivalent | Reconstruct maximal-extension layer upward |
| Hahn depth 4 | Foundational imports only | Reconstruct the complete local scaffold |
| Rank-nullity | Exact final theorem hidden | Complementary local-recombination task |
| Intermediate value | Three local IVT interfaces hidden | Complementary alternate-route task |

These are **canonical-path frontiers**, not complete theorem-DAG layers. The
numeric labels on rank-nullity and intermediate value are family-local and
cannot be pooled into the Hahn-Banach depth curve.

`validate_templates.py` checks that every hidden declaration is unavailable
under its task imports and compiles a canonical reconstruction against every
template. Thus all tasks are satisfiable in the pinned environment.

### Generation and verification

- The primary model was the Codex model `gpt-5.6-sol`, invoked at high reasoning
  effort. A small comparison used `gpt-5.5` at the same setting.
- Each run used a fresh, ephemeral directory. Shell, browser, web, app,
  code-host, and related tools were disabled. The model received the fixed
  template and, only in adaptive runs, the previous Lean diagnostic.
- Each attempt had a 900-second model timeout and a 180-second Lean timeout.
  A fixed cap does not imply equal actual compute: token use and completion time
  varied substantially.
- Exact type wrappers and `#print axioms` enforce the target type and axiom
  closure. The runner rejects `sorry`, `admit`, injected axioms, unsafe or
  opaque declarations, native decision bypasses, compile-time I/O/meta commands,
  and unexpected axioms.

An audit found two protocol limitations. First, one successful library-baseline
trial logged a rejected empty `apply_patch` attempt. It changed nothing and the
returned proof independently verifies, but that trial is not strictly free of
attempted tool activity. No redacted trial did this. Second, candidate execution
is protected by static screening rather than an OS-level filesystem sandbox.
None of the exact candidates used I/O or metaprogramming.

Raw response/event streams are excluded from Git because they contain model
reasoning. The exact Lean candidates are independently recompilable, but the
generation-side tool restrictions are supported by runner configuration,
curated result metadata, and the explicit protocol note rather than published
raw streams.

## Results

### Independent one-shot trials

All rows below are fresh sessions with `max_attempts=1`.

| `gpt-5.6-sol` task | Verified | Median model time |
|---|---:|---:|
| Matched narrow-import Hahn control | 3/3 | 5.734 s |
| Named Hahn theorem imported | 5/5 | 20.922 s |
| Rank-nullity target redacted | 3/3 | 38.078 s |
| Intermediate-value interfaces redacted | 1/3 | 152.719 s |
| Hahn depth 1 | 0/3 | 308.578 s |
| Hahn depth 2 | 0/3 | 353.781 s |
| Hahn depth 3 | 0/3 | 412.469 s |
| Hahn depth 4 | 0/5 | 338.765 s |

The core Hahn-Banach comparison is one theorem family tested repeatedly: eight
one-shot control trials and fourteen one-shot reconstruction trials across four
frontiers. Those repetitions estimate reliability on this target; they do not
provide the theorem diversity of a broad benchmark.

The primary matrix before adding the matched control contained 25 trials and
used 396,678 input tokens plus 224,298 output tokens. The three matched controls
add 26,561 input and 510 output tokens.

The strongest within-target observation is the discontinuity between direct
theorem availability, 8/8 across two controls, and any Hahn-Banach
reconstruction, 0/14. The 8/8 controls are not eight from-scratch proofs: they
show that the model can recognize and use the finished result when it is
available. The matched control rules out the full extension-module import as
the sole explanation because the model can connect a renamed premise to the
exact goal under the same narrow imports.

The result does **not** show progressive degradation from depth 1 to depth 4.
Every redacted tier is already at the floor. More samples, easier intermediate
frontiers, or a stronger interaction policy are needed to estimate a curve.

The complementary tasks matter. Rank-nullity passed 3/3, although every success
used the same compact quotient-equivalence route as mathlib and may reflect
memorization or familiar local recombination. The intermediate-value success is
stronger evidence of reconstruction: it used a direct connected-image
separation argument rather than rebuilding the hidden canonical interface
chain.

### Compiler-guided repair

Attempts within one conversation are adaptive and dependent. They are not
additional pass@k samples.

| `gpt-5.6-sol` Hahn frontier | Attempt sequence | Final result | Total model time |
|---|---|---:|---:|
| Depth 1 | fail, pass | Verified | 411.031 s |
| Depth 2 | fail, fail, fail | Unverified | 724.171 s |
| Depth 3 | fail, fail, fail | Unverified | 850.594 s |
| Depth 4 | fail, fail, fail | Unverified | 765.673 s |

The verified depth-1 declaration depends only on Lean's expected core axioms,
the supplied Riesz frontier, and `Quot.sound`. It contains no bypass. This is a
direct counterexample to reading "unable" as "cannot produce a proof even with
modest compiler feedback."

Failed candidates often recovered the recognizable cone, maximal-extension,
and Zorn architecture. They broke on `PointedCone` fields, `LinearPMap`
construction and ordering, subtype transport, definitional equality, linearity
obligations, and occasionally nonexistent helper names. The failures therefore
combine global decomposition with mathlib interface fluency; they are not clean
evidence of informal mathematical ignorance.

### Small model comparison

A separate `gpt-5.5` one-shot check passed the named Hahn baseline and failed
one trial each on redacted rank-nullity, intermediate value, and Hahn depth 1:
1/4 overall. With one sample per condition it is only corroborative. An earlier
`gpt-5.4` trajectory passed a shallow algebra plumbing control and failed all
three adaptive depth-1 attempts; its first candidate was initially
misclassified because an informational todo event was treated as a tool, but
recompiling the preserved source still fails.

## External evidence

The closest primary research supports a real premise, context, and
long-horizon gap, while also showing why a universal inability claim is too
strong:

- [TaoBench](https://arxiv.org/html/2603.12744) contains 150 paired
  undergraduate-analysis problems. Across specialized provers, pass@128 drops
  from 69.33% to 41.33% for DeepSeek-Prover-V2-7B, 70.67% to 37.33% for
  Goedel-Prover-V2-8B, and 72.67% to 49.33% for its 32B version when moving
  from mathlib formulations to the benchmark's from-scratch framework. This is
  definitional shift, not theorem-declaration redaction, but it strongly
  supports the generalization concern.
- [TheoremBench](https://arxiv.org/html/2606.09450) compares standalone final
  statements with dependency-aware tasks that expose supporting results as
  explicit premises. Capable provers improve substantially when the premises
  are supplied. It is the closest inverse of declaration redaction, though
  its premised dataset also expands targets into subtheorems.
- [VeriSoftBench](https://arxiv.org/html/2602.18307) studies 500
  repository-scale software-verification obligations. Average project
  dependencies grow from 11.58 direct to 37.93 transitive references; the paper
  reports that long dependency chains, rather than nearby symbol count alone,
  correlate with lower success. This is repository verification, not
  mathematical reconstruction.
- [MA-ProofBench](https://arxiv.org/html/2606.13782) reports `gpt-5.5` at 6.5%
  Pass@1 and 16% Pass@8 on undergraduate analysis, falling to 1.75% and 5% on
  its PhD-level tier. Advanced analysis remains far from saturated.
- [MathlibLemma](https://arxiv.org/abs/2602.02561) reports 1,506
  bypass-screened, Lean-checked generated folklore proofs and a benchmark of
  4,028 statements. Models demonstrably can create missing mathematical
  connective tissue.
- [CAM-Bench](https://arxiv.org/html/2605.17255) gives long-horizon,
  compiler-interactive systems up to eight hours per task. M2F verifies 143/200
  and Aristotle 125/200 sampled tasks, far above direct baselines. Remaining
  failures are dominated by missing infrastructure, library grounding, type
  discipline, and proof decomposition, closely matching the local diagnostics.
- [LeanMarathon](https://arxiv.org/html/2606.05400) is the strongest
  counterweight to categorical long-proof claims. A multi-agent `gpt-5.5`
  system formalizes all seven research targets in its evaluation, producing
  258 lemmas and theorems without `sorry`. Its three runs use 245M to 796M
  tokens and critical paths of roughly 11.5 to 40.7 hours. This does not answer
  the fixed-budget, closed-book Hahn-Banach test; it shows that long-horizon
  success is possible under a substantially different harness, decomposition,
  tool, and compute regime.

These studies support sensitivity to premise availability and long-horizon
structure, but none establishes a monotonic declaration-depth law.

## Limitations

- The sample is small and not statistically powered.
- At the theorem-family level, the four-frontier experiment is an `n=1` case
  study. Hahn-Banach is the only family with a depth series; repeated trials do
  not change that scope.
- The series follows one canonical proof path, not an exhaustive theorem DAG.
- Alternate declarations and routes may survive redaction; the IVT success
  demonstrates why canonical depth is not intrinsic difficulty.
- The prompt exposes task names, frontier descriptions, and numeric tiers.
- Public mathlib statements and proofs may be represented in pretraining.
- The model alias has no immutable snapshot or controllable seed.
- Most historical trials predate per-attempt source hashes, and the exact
  pre-hardening runner file was not archived. The curated manifest pins the
  preserved sources at curation time but cannot prove a byte-for-byte
  precuration chain of custody.
- One-shot failures do not imply failures under search, retrieval, Lean tools,
  multi-agent decomposition, or a larger budget.
- No alternative commercial model, specialist prover, or human-expert baseline
  was run.
- Hahn-Banach is commonly graduate functional analysis, not a universal
  undergraduate topic. Rank-nullity and IVT are cleaner undergraduate checks.
- Static screening and post-hoc candidate audit are not a substitute for an
  OS-level sandbox around untrusted Lean metaprogramming.

## Final assessment

Ordinary theorem completion can hide whether a system can reconstruct a
missing hierarchy of interfaces and lemmas. The local data find a large
observed dependency-availability gap across these Hahn-Banach trials and
failure modes consistent with that mechanism.

They do not establish an impossibility result, a universal frontier-model
boundary, or the proposed depth-scaling law. The most defensible reading is:
**in this Hahn-Banach one-shot setting, the dependency-interface bottleneck is
directionally supported, but categorical inability is not supported once
compiler-guided repair and long-horizon systems are included.**

Exact candidates, diagnostics, run metadata, hashes, exclusions, and protocol
notes are in [the curated evidence](benchmark/evidence/README.md).
