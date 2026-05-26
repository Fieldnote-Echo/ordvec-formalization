# ordvec-formalization

A Lean 4 formalization of the finite monotone-decision theorem behind the
**OrdVec / RankQuant candidate-generator mechanism**: under positive common
support and monotone likelihood ratio, the Bayes-optimal deterministic rule is
a threshold on the ordered finite statistic. All public declarations live in
the `OrdvecFormalization` namespace.

Seeded from [`takens-formalization`](../takens-formalization) and pinned to the
same toolchain (Lean `v4.28.0`, Mathlib `v4.28.0`) so lemmas port across without
a version bump. Sibling to `reccs-/cd-/fd-formalization`.

> **Status: first milestones proved.** The finite Bayes-threshold spine builds
> without proof placeholders: finite upper sets are thresholds, cross-multiplication MLR
> makes the Bayes admit predicate monotone, and the resulting threshold
> minimizes finite Bayes risk by a pointwise `Finset.sum_le_sum` argument.
> A reusable exponential-tilt layer now proves that positive finite base weights
> tilted by `exp (θ * x)` satisfy MLR as `θ` increases.
> The feasible FNCH support is instantiated as shifted `Fin (hi - lo + 1)` with
> strictly positive binomial base weights, and the paper-facing overlap-null
> layer states threshold optimality for literal actual-overlap FNCH weights.
> Bayes priors are represented by the bundled `Prior` type.

## What it proves

1. **Finite threshold representation.**
   A monotone predicate on `Fin (n + 1)` is represented by a cut in
   `Fin (n + 2)`, including the accept-all and reject-all boundary cases.
2. **MLR to monotone Bayes admit predicate.**
   Cross-multiplication MLR on positive `ℝ≥0` PMFs implies the pointwise Bayes
   decision predicate is monotone. The proof avoids division in the statement
   and uses positivity only to cancel the common `p0.mass x` factor.
3. **Bayes-optimal threshold.**
   The threshold selected by the pointwise Bayes predicate minimizes the finite
   Bayes risk among all deterministic admit sets.
4. **Exponential tilt has MLR.**
   Positive base weights on the finite support, normalized after tilting by
   `exp (θ * x)`, satisfy cross-multiplication MLR for `θ₀ ≤ θ₁`. The same file
   composes this with the Bayes theorem to get threshold optimality for tilted
   families.
5. **FNCH feasible-support instantiation.**
   For parameters `k ≤ N` and `draws ≤ N`, the feasible overlap interval
   `[k + draws - N, min k draws]` is shifted to a finite support. The binomial
   base weights are strictly positive there, so the exponential-tilt theorem
   gives MLR and Bayes-optimal threshold rules for FNCH.
6. **Actual-overlap threshold statement.**
   Shifted thresholds are proved equivalent to thresholds on the actual overlap
   count `lo + x`, giving paper-facing names in `OverlapNull.lean`.
7. **Literal actual-overlap FNCH weights.**
   The PMF with weights
   `choose k x * choose (N-k) (draws-x) * exp(θ*x)` is proved equal pointwise
   to the shifted-coordinate tilt after normalization, so the final theorem
   surface no longer mentions the shifted implementation detail.
8. **Reviewer-facing theorem shape.**
   The final citation theorem uses a strict parameter inequality `θ₀ < θ₁`, a
   bundled `Prior`, and a threshold in actual overlap coordinates:
   `OrdvecFormalization.overlapNull_threshold_isBayesOptimal`.
   Paper-language aliases are also checked:
   `literal_fnch_overlap_has_mlr`, `fnch_overlap_admit_threshold`, and
   `fnch_overlap_threshold_bayes_optimal`.

The reviewer-facing statement map is in [`docs/theorem-map.md`](docs/theorem-map.md).
The dashboard in [`OrdvecFormalization/Verify.lean`](OrdvecFormalization/Verify.lean)
checks the theorem names and prints the axiom audit for:

```lean
Prior
mlr_monotone_bayesAdmit
bayesAdmit_isThreshold
threshold_bayesRisk_optimal
exponentialTilt_hasMLR
exponentialTilt_hasMLR_of_lt
exponentialTilt_bayesAdmit_isThreshold
exponentialTilt_threshold_bayesRisk_optimal
fnch_hasMLR
fnch_hasMLR_of_lt
fnch_bayesAdmit_isThreshold
fnch_threshold_bayesRisk_optimal
fnch_bayesAdmit_isActualOverlapThreshold
fnch_actualOverlapThreshold_bayesRisk_optimal
fnchActualPMF_mass_eq_fnchPMF_mass
fnchActual_hasMLR
fnchActual_hasMLR_of_lt
fnchActual_bayesAdmit_isActualOverlapThreshold
fnchActual_actualOverlapThreshold_bayesRisk_optimal
fnchActual_bayesAdmit_isActualOverlapThreshold_of_lt
fnchActual_actualOverlapThreshold_bayesRisk_optimal_of_lt
overlapNull_fnch_hasMLR
overlapNull_bayesAdmit_isThreshold
overlapNull_threshold_bayesRisk_optimal
overlapNull_threshold_isBayesOptimal
literal_fnch_overlap_has_mlr
fnch_overlap_admit_threshold
fnch_overlap_threshold_bayes_optimal
```

Expected axioms are only Lean's standard kernel baseline:
`[propext, Classical.choice, Quot.sound]`.

Empirical null calibration and the broader OrdVec overlap interpretation remain
deferred; the current proved surface is the finite Bayes threshold theorem
instantiated for literal FNCH overlap weights.

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

## File layout

```text
OrdvecFormalization/
├── FiniteDecision.lean
├── MLR.lean
├── BayesThreshold.lean
├── ExponentialTilt.lean
├── FNCH.lean
├── OverlapNull.lean       # paper-facing theorem surface
├── Examples.lean
└── Verify.lean
docs/
└── theorem-map.md
```

## Future Mathlib / project layers

`N1` hypergeometric PMF · `N5` MLR for one-parameter exponential families ·
`N6` Neyman–Pearson lemma · `N7` Karlin–Rubin.

## Build

```sh
lake update     # fetches Mathlib v4.28.0 (first run; large)
make build
make verify
make audit
make lint
```

## Licensing

Apache-2.0; see [`LICENSE`](LICENSE).
