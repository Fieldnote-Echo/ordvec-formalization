# ordvec-formalization

A Lean 4 formalization of the **OrdVec / RankQuant candidate-generator mechanism**
(paper §6): the bitmap popcount-overlap statistic `X = |Q_top ∩ D_top|` and the
**optimality of the threshold admission rule** `admit ⇔ X > t★`.

Seeded from [`takens-formalization`](../takens-formalization) and pinned to the
same toolchain (Lean `v4.28.0`, Mathlib `v4.28.0`) so lemmas port across without
a version bump. Sibling to `reccs-/cd-/fd-formalization`.

> **Status: SCAFFOLD.** Statements are drafts (`sorry`-stubbed) in
> [`OrdvecFormalization/OverlapNull.lean`](OrdvecFormalization/OverlapNull.lean);
> nothing is built yet. `import Mathlib` is the catch-all import — narrow once the
> proofs settle.

## What it proves (targets)

1. **MLR (combinatorial core).** The Fisher noncentral hypergeometric overlap
   family has a monotone likelihood ratio in `X` — the pmf ratio in the
   noncentrality `θ` is `exp((θ₂−θ₁)·x)` up to an `x`-independent constant.
2. **UMP (frequentist).** Given MLR, the one-sided threshold test is uniformly
   most powerful (Karlin–Rubin).
3. **Bayes-optimal threshold (recommended primary route).** Under 0–1 loss the
   Bayes decision boundary is a single threshold on `X`. Reuses Mathlib
   `bayesRisk` / `posterior` / `boolKernel`; **cheaper than the full UMP tower**
   (the Neyman–Pearson lemma is the dominant missing-from-Mathlib piece), so the
   Bayes route is the launch target.

Upgrades the paper's §6 from a *computed selectivity / false-positive rate*
("mechanism, not theorem") to *the popcount threshold is the provably optimal
admission rule* under the stated alternative.

## Why now — empirical grounding

The MLR precondition is not assumed; it was **validated on real arXiv embeddings**
in the `ordvec` repo (branch `experiment/st-f-correlated-cb`): the overlap
stochastically dominates the empirical null and the likelihood ratio is monotone
non-decreasing in `X` (0/34 violations, LR 0.003 → 317.5). That green-lit this
project. See `ordvec/docs/EXPERIMENTS.md` on the experiment branches.

## Scope discipline (important)

The theorem concerns the admission **rule** given an abstract null `H₀` (`θ = 0`).
It is **not** a claim that the textbook hypergeometric is the deployment null:
on real embeddings the null overlap is *mean-shifted* (≈105 vs hypergeometric 64)
more than it is variance-inflated (branches `experiment/st-e-null-calibration`,
`experiment/st-f-correlated-cb`). That mean/spread mismatch is a corpus
**calibration** matter for the paper's selectivity section, **not** part of the
optimality theorem. Keep them distinct in the formalization.

## Missing-from-Mathlib spin-off PRs

`N1` hypergeometric PMF · `N5` MLR for one-parameter exponential families ·
`N6` Neyman–Pearson lemma · `N7` Karlin–Rubin. (The Bayes route needs only a
subset; prefer it.)

## Build

```sh
lake update     # fetches Mathlib v4.28.0 (first run; large)
lake build
```

## Licensing

Intended dual **MIT OR Apache-2.0**, matching `ordvec`. Add `LICENSE` /
`LICENSE-APACHE-2.0` before any public release. (Not yet added — local seed.)
