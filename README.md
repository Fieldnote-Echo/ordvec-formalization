# ordvec-formalization

[![Lean CI](https://github.com/Fieldnote-Echo/ordvec-formalization/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Fieldnote-Echo/ordvec-formalization/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of a finite Bayes-threshold theorem for OrdVec-style
overlap decisions.

## What This Means

If two positive finite distributions have monotone likelihood ratio, then the
Bayes-optimal deterministic rule is a threshold on the ordered statistic.

For the OrdVec use case, the statistic is overlap count. The formalized FNCH
instantiation says: under a literal Fisher noncentral hypergeometric overlap
model with `theta0 < theta1`, the Bayes-risk-minimizing deterministic admission
rule is a threshold in the actual overlap count.

In plain terms: under the modeled monotone-likelihood-ratio condition, the
formal proof justifies a popcount-style cutoff rule rather than an arbitrary
accept/reject pattern.

## Main Checked Theorem

```lean
OrdvecFormalization.overlapNull_threshold_isBayesOptimal
```

Paper-language alias:

```lean
OrdvecFormalization.fnch_overlap_threshold_bayes_optimal
```

The theorem quantifies over all deterministic admission sets on the feasible
overlap support and produces a threshold set with Bayes risk no larger than any
of them.

The reviewer-facing theorem map is in
[`docs/theorem-map.md`](docs/theorem-map.md).

## Proof Spine

- `FiniteDecision.lean`: monotone predicates on `Fin (n + 1)` are thresholds.
- `MLR.lean`: cross-multiplication MLR makes the Bayes admit predicate monotone.
- `BayesThreshold.lean`: the Bayes-admit threshold minimizes finite Bayes risk.
- `ExponentialTilt.lean`: positive finite exponential tilts have MLR.
- `FNCH.lean`: literal actual-overlap FNCH weights match the shifted tilt after
  normalization.
- `OverlapNull.lean`: paper-facing theorem names.
- `Verify.lean`: public-name checks and axiom audit.

Expected axiom baseline:

```text
[propext, Classical.choice, Quot.sound]
```

## Scope

This proves an optimality theorem for the admission rule under the stated finite
model. It does not prove that the textbook hypergeometric is the deployment null
for real embeddings, and it does not include randomized tests, Neyman-Pearson,
UMP, Karlin-Rubin, or empirical null calibration.

Those are separate layers. This repository is the finite deterministic
Bayes-threshold layer.

## Build

Pinned to Lean `v4.28.0` and Mathlib `v4.28.0`.

```sh
lake update     # first run only; fetches Mathlib
make build
make verify
make audit
make lint
```

GitHub Actions runs the same build, verification, audit, and linter checks in
[`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml).

## License

Apache-2.0; see [`LICENSE`](LICENSE).
