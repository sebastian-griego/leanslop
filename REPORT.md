# What the X thread is claiming

## Bottom line

Doomslide is not claiming that LLMs cannot solve undergraduate exercises,
generate Lean proofs, or help formalize textbooks. He is proposing a
dependency-ablation test of a narrower capability:

1. Choose a theorem already represented in mathlib.
2. Remove the theorem and intermediate lemma declarations in its dependency
   graph, at increasing graph distances.
3. Ask a model to reconstruct the missing proof infrastructure and observe how
   success changes with redaction depth.

He does not specify a sampling metric, context policy, or compute budget. A
rigorous implementation should hold those conditions fixed and report verified
pass@k at each depth.

The implied hypothesis is that performance will worsen as the missing
dependency chain gets deeper. The alleged weakness is global proof architecture
and interface design, not local tactic selection or short mathematical insight.

This interpretation is strongly supported by the thread. His broader
categorical wording, however, is not established by evidence he supplies there:
he cites personal periodic checks, gives no harness or results, and names only
Hahn-Banach as a concrete wager.

## Relevant X context

The focal post is the end of this reply chain:

- [Root](https://x.com/doomslide/status/2078858292709728700): current LLMs
  allegedly cannot construct some undergraduate mathlib material despite
  training exposure and benchmark optimization.
- [Request for a source](https://x.com/pli_cachete/status/2078858550017728950).
- [Doomslide's answer](https://x.com/doomslide/status/2078858854339604729):
  he checks periodically, knows of no paper, and wants to be proven wrong.
- [Key clarification](https://x.com/doomslide/status/2078859195491700903):
  the task is proving a theorem without its intermediate lemmas.
- [Sebastian offers to test it](https://x.com/sebngriego/status/2078866002281160981).
- [Focal reply](https://x.com/doomslide/status/2078869136017387781):
  redact to several dependency-graph depths and observe scaling.

Other posts narrow the intended claim:

- [Hahn-Banach is the concrete example](https://x.com/doomslide/status/2078863424621039871).
- [The task is not supposed to be superhuman](https://x.com/doomslide/status/2078862503459557856);
  he claims most professors could reconstruct it given time.
- [Benchmarks allegedly select for shallow problems](https://x.com/doomslide/status/2078864081360998730).
- ["Shallow" means how far one must step away from the stated problem](https://x.com/doomslide/status/2078868416916574211).
- [Long, locally simple but globally deep arguments are the predicted weak
  point](https://x.com/doomslide/status/2078868027844518050).

The root is a pushback against an AI-math hype chain:

- [Edgar Dobriban](https://x.com/EdgarDobriban/status/2077082912021786660)
  reports a GPT-5.6-assisted result in false-discovery-rate theory.
- [Noam Brown](https://x.com/polynoamial/status/2077762676932165996)
  quotes that result and extrapolates from recent model progress.
- [Alek Dimitriev](https://x.com/tensor_rotator/status/2078335791156310369)
  predicts the next Fields Medal will be the last awarded to humans.
- [Christian Szegedy](https://x.com/ChrSzegedy/status/2078624857223536824)
  repeats the prediction.

[Szegedy later explains](https://x.com/ChrSzegedy/status/2078829215185768810)
that his prediction is partly institutional: AI-heavy collaboration may make
credit assignment incompatible with the medal's purpose. That is distinct from
doomslide's narrower capability claim.

Two counterexamples raised in the replies do not run the proposed test:

- The [Claude-assisted Axler companion](https://github.com/rkirov/linear-algebra-done-right-lean)
  uses mathlib directly and receives roughly one to two hours of line-by-line
  human review per subsection.
- A reply
  [asserts that Codex, Claude, GPT-5.6, and Fable can do the task](https://x.com/emmetics/status/2078869893131452772),
  but supplies no depth-controlled result. Reports of strong solutions do not
  measure reconstruction under controlled removal of a long dependency
  hierarchy.

## What a valid test must remove

Hiding proof bodies is insufficient. If the lemma declarations remain
callable, the model can use them without reconstructing their content.

A defensible test should:

- measure theorem-DAG distance, not raw file-import depth;
- retain definitions and types while removing proposition declarations;
- prevent alternate declarations whose dependency closure contains a redacted
  lemma;
- prohibit source lookup during generation;
- hold the model, context, verifier access, sampling count, and compute budget
  fixed;
- compile every candidate and reject `sorryAx` or other proof bypasses.

In mathlib `v4.32.0`, the relevant local chain is:

```text
exists_extension_of_le_sublinear
  -> riesz_extension
    -> RieszExtension.exists_top
      -> RieszExtension.step
```

See mathlib's
[extension source](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Convex/Cone/Extension.lean)
and the
[normed-space wrapper](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Normed/Module/HahnBanach.lean).

## Local spot check

The repository contains four path-ablation templates plus a positive control.
They approximate increasing dependency depth along mathlib's canonical local
proof path; they do not compute or remove a complete theorem-DAG layer. Known
mathlib proofs were adapted to compile against every template, and an import
check confirmed the original redacted declarations were absent.

Test conditions:

- Model: `gpt-5.4` through the authenticated Codex/ChatGPT CLI.
- API keys: none. The runner removes every `*_API_KEY` variable and requires
  Codex to report ChatGPT authentication before starting.
- Generation access: no shell, filesystem, browser, or web search.
- Verifier: Lean `v4.32.0`, mathlib `v4.32.0`.
- Bypasses: `sorry`, `admit`, new axioms, `opaque`, `unsafe`, and `sorryAx`
  are rejected.

Results:

| Task | Available proof infrastructure | Attempts | Verified |
|---|---|---:|---:|
| Shallow control: `2xy <= x^2 + y^2` | Standard real arithmetic | 1 | 1 |
| Real Hahn-Banach core | M. Riesz extension supplied | 3 | 0 |

The control passed on its first attempt. All three sequential Hahn-Banach
attempts in one repair conversation failed Lean checking at the shallowest
redaction tier. Because that tier produced no success in this small run, deeper
tiers could not show a further decline and were not run. The focal scaling
prediction therefore remains untested.

One runner detail is worth recording: an informational Codex `todo_list` event
was initially classified as forbidden even though it exposed no external
information. That first candidate was compiled after correcting the
classification and also failed. Only one later candidate therefore received
actual Lean compiler diagnostics during generation. This makes the result an
exploratory failure case, not three independent samples or a pass@k estimate.
The algebra control checks only the model/CLI/compiler plumbing; it is not
comparable in difficulty or imports to Hahn-Banach.

An audit found that the original runner expressed required signatures only in
comments. The generated candidates did attempt the full requested signatures,
but the harness has since been hardened with compiled type wrappers and axiom
closure checks. Rechecking the exact preserved completions under the hardened
verifier leaves the outcome unchanged: the control passes and the three
Hahn-Banach attempts fail. See the
[curated evidence](benchmark/evidence/README.md).

The original summary artifacts preserve model, authentication, token, timing,
and repair-history metadata. Raw Codex event streams are not committed because
they include model reasoning, so the no-tool condition is documented by the
runner configuration rather than independently auditable event logs.

## External evidence

Recent primary research supports the direction of the hypothesis:

- [MA-ProofBench](https://arxiv.org/html/2606.13782) reports that miniF2F has
  reached 100% for one system, while the best evaluated model, GPT-5.5, reaches
  only 16% Pass@8 on 100 undergraduate analysis tasks and 5% on 100 Ph.D.-level
  tasks. The paper identifies incomplete proofs and mathlib hallucinations as
  dominant failure modes.
- [TaoBench](https://arxiv.org/html/2603.12744) pairs 150 undergraduate
  analysis exercises using Tao's from-scratch framework with mathematically
  equivalent mathlib formulations. Performance falls by roughly 26% on
  average in the from-scratch formulation.
- [TheoremBench](https://arxiv.org/html/2606.09450) finds that explicitly
  supplying intermediate premises substantially improves proof success for
  capable provers.
- [VeriSoftBench](https://arxiv.org/abs/2602.18307), a repository-scale formal
  software-verification benchmark rather than a math-redaction experiment,
  observes that success is negatively associated with large, multi-hop
  transitive dependency closures.

There is also important counterweight:

- [MathlibLemma](https://arxiv.org/abs/2602.02561) reports 1,506 Lean-checked,
  bypass-screened folklore lemmas generated by an LLM pipeline. Models can
  create useful missing connective tissue; the claim cannot reasonably be
  "models never construct intermediate lemmas."

## Assessment

The best-supported conclusion is:

- **High confidence:** the focal post proposes progressive dependency
  redaction as a test of hierarchical proof reconstruction.
- **High confidence:** ordinary proof-completion scores overstate performance
  when familiar definitions, premises, or repository context are removed.
- **Low-to-moderate confidence:** Hahn-Banach-like deep formal developments are
  a plausible weakness for current systems. The local `gpt-5.4` failure and
  recent benchmarks point in this direction, but the run did not measure a
  depth curve.
- **Low confidence in the universal wording:** the thread does not prove that
  every current frontier model is unable to reconstruct such material.
  `gpt-5.6` and Claude Fable were not locally tested, and one target/model run
  cannot establish a model-family capability boundary.

Hahn-Banach is also more often taught in graduate functional analysis than in
a universal undergraduate curriculum. That weakens the rhetoric around
"undergraduate parts," but not the proposed dependency-depth experiment.
