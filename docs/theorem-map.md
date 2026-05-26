# Theorem Map

This document maps the reviewer-facing claim to the checked Lean theorem
surface. It is deliberately narrower than the OrdVec paper narrative: the
formalization proves a finite Bayes decision theorem and its literal FNCH
overlap instantiation.

## Citation Claim

For a literal Fisher noncentral hypergeometric overlap model with parameters
`theta0 < theta1`, the Bayes-risk-minimizing deterministic admission rule is a
threshold in the actual overlap count.

Checked theorem:

```lean
OrdvecFormalization.overlapNull_threshold_isBayesOptimal
```

Paper-language alias:

```lean
OrdvecFormalization.fnch_overlap_threshold_bayes_optimal
```

The theorem quantifies over:

- `p : FNCHParams`, carrying `k <= N` and `draws <= N`.
- `theta0 theta1 : Real`, with strict hypothesis `theta0 < theta1`.
- `prior : Prior`, a bundled prior probability for `H1`.
- all deterministic admission sets `R : Set p.support`.

It produces a cut `cut : Fin (p.hi - p.lo + 2)` such that the
actual-overlap threshold set has Bayes risk no larger than any deterministic
admission set.

## Proof Spine

1. `FiniteDecision.lean`
   `exists_threshold_of_monotone_pred` proves that every monotone predicate on
   `Fin (n + 1)` is represented by a threshold cut in `Fin (n + 2)`. The two
   extra boundary cuts encode accept-all and reject-all rules.

2. `MLR.lean`
   `HasMLR` states monotone likelihood ratio by cross multiplication:
   `p1 x * p0 y <= p1 y * p0 x` for `x <= y`.
   `mlr_monotone_bayesAdmit` proves that this makes the pointwise Bayes admit
   predicate monotone. Positivity of `p0.mass x` is used exactly at the final
   cancellation step.

3. `BayesThreshold.lean`
   `bayesAdmit_isThreshold` turns monotone Bayes admission into a threshold.
   `threshold_bayesRisk_optimal` proves optimality by `Finset.sum_le_sum`,
   since finite Bayes risk decomposes pointwise over support points.

4. `ExponentialTilt.lean`
   `exponentialTilt_hasMLR` proves that positive finite base weights tilted by
   `exp (theta * x)` have MLR as `theta` increases.

5. `FNCH.lean`
   `fnchActualPMF_mass_eq_fnchPMF_mass` connects literal actual-overlap FNCH
   weights
   `choose k x * choose (N-k) (draws-x) * exp(theta*x)`
   to the shifted exponential-tilt implementation after normalization.
   `fnchActual_actualOverlapThreshold_bayesRisk_optimal_of_lt` gives the
   strict-parameter FNCH threshold optimality theorem.

6. `OverlapNull.lean`
   `overlapNull_threshold_isBayesOptimal` is the citation theorem. The final
   aliases in that file keep paper-language names available without duplicating
   the proof.

## Public Names

Core theorem names:

- `mlr_monotone_bayesAdmit`
- `bayesAdmit_isThreshold`
- `threshold_bayesRisk_optimal`
- `exponentialTilt_hasMLR`
- `fnchActualPMF_mass_eq_fnchPMF_mass`
- `overlapNull_threshold_isBayesOptimal`

Paper-language aliases:

- `literal_fnch_overlap_has_mlr`
- `fnch_overlap_admit_threshold`
- `fnch_overlap_threshold_bayes_optimal`

## What Is Not Claimed

- No empirical null calibration theorem is formalized here.
- No claim is made that the textbook hypergeometric is the deployment null for
  real embeddings.
- No randomized tests, Neyman-Pearson lemma, UMP statement, or Karlin-Rubin
  theorem is included in this milestone.
- No asymptotic or measure-theoretic probability result is used; the proof is
  finite and deterministic over `Fin`.

## Reviewer Checks

Run:

```sh
make build
make verify
make audit
make lint
```

`make verify` checks all public theorem names and prints their axiom audit.
Expected axioms are Lean's standard baseline:

```text
[propext, Classical.choice, Quot.sound]
```

