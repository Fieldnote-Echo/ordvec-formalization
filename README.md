# ordvec-formalization

[![Lean CI](https://github.com/Fieldnote-Echo/ordvec-formalization/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Fieldnote-Echo/ordvec-formalization/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of finite decision rules for constant-weight bitmap
overlap: under a canonical finite overlap-tilt signal model with a uniform
constant-weight bitmap null, an overlap-tail rule is Bayes-optimal and its null
probability is exactly hypergeometric.

The repository is meant to serve two audiences:

- reviewers who want to inspect the precise mathematical claim and its axiom
  footprint;
- implementers who want a checked finite model for constant-weight bitmap
  overlap thresholds and exact null calibration.

## Checked Theorem

Strongest literal-null theorem:

```lean
OrdvecFormalization.exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
```

In words:

```text
Under a finite canonical signal model where the null is the uniform law over
K-active bitmaps and the signal law exponentially tilts that law by literal
bitmap overlap, a literal overlap-tail rule is Bayes-optimal among all
deterministic admission rules.

The same threshold event has exactly the hypergeometric upper-tail probability
under the model null.
```

Cost-sensitive version:

```lean
OrdvecFormalization.exists_uniformBitmapOverlapTail_finiteCostedBayesRisk_le_and_hypergeomTail
```

General positive-base version:

```lean
OrdvecFormalization.exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
```

## What This Means

If two positive finite distributions have monotone likelihood ratio, then the
Bayes-optimal deterministic rule is a threshold on the ordered statistic.

For the constant-weight bitmap specialization, the statistic is literal overlap
count. The formalized overlap-null instantiation says: under a literal Fisher
noncentral hypergeometric overlap model with `theta0 < theta1`, the
Bayes-risk-minimizing deterministic admission rule is a threshold in the actual
overlap count.

In plain terms: under the modeled monotone-likelihood-ratio condition, the
formal proof justifies a popcount-style cutoff rule rather than an arbitrary
accept/reject pattern.

The strongest checked theorem specializes this to the concrete constant-weight
bitmap setting: the full observation space is the finite type of `K`-active
bitmaps, the statistic is literal overlap with a fixed `K`-active bitmap, and
the Bayes-optimal pulled-back quotient threshold is exactly the bitmap overlap
tail event whose null probability is the hypergeometric tail.

## Plain-English Framing

The claim is not that ordinal signatures contain all semantic information in an
embedding. The claim is task-relative:

```text
full observation Z
quotient Q(Z)
binary target Y
```

If the decision evidence satisfies

```text
P(Y | Z) = P(Y | Q(Z))
```

or, equivalently in the finite likelihood-ratio form used here, the class
likelihood ratio factors through the quotient, then no Bayes-relevant decision
information is lost by using the quotient. Under the additional monotonicity
condition, the optimal quotient rule is a threshold on overlap evidence.

This is a theory of **decision sufficiency through a quotient**, not
**representation completeness**. Full observations may still be essential for forming,
transforming, training, calibrating, and composing semantic representations.
They can carry margins, near-ties, residual features, confidence, and other
signals that matter for tasks beyond candidate admission. The formal result
says only that, for a binary admission decision satisfying the stated
statistical contract, the decision surface can factor through an order-like
quotient.

This is the same broad scientific pattern as rank statistics, AUC, ordinal
utility, permutation entropy, and other quotient-based methods: full metric
structure may be needed to generate the state, while a lower-dimensional
order-like invariant can be enough for a targeted recognition or decision
problem.

## Relation To OrdVec

OrdVec candidate generation asks whether an observed overlap count is large
enough to admit a candidate. This repository proves that, under the finite
positive-support MLR model used in the OrdVec analysis, the optimal deterministic
Bayes rule has exactly that shape: accept at or above a threshold and reject
below it.

So the formal result supports the structure of the OrdVec popcount cutoff. It is
not a benchmark, not an implementation proof for the Rust crate, and not a claim
that every dataset follows the model. Those belong in the main
[`ordvec`](https://github.com/Fieldnote-Echo/ordvec) repository's tests,
benchmarks, and empirical validation.

If you are evaluating the crate for a candidate-admission implementation, read this as a
decision-theoretic sanity check on the shape of the candidate filter. The proof
says the cutoff form is the right deterministic rule under the model; your
deployment decision should still use the crate's benchmarks and your own recall,
latency, and memory measurements.

For an implementation that uses constant-weight overlap admission, the practical
message is narrow:

- the candidate-admission rule can be a cheap overlap threshold when the
  class evidence is well-modeled by a monotone overlap signal;
- threshold tail behavior has an exact finite null model under the
  idealized independent constant-weight bitmap law;
- full observations remain important for targets that are not captured by the
  modeled admission decision.

## Checked Names

Primary theorem:

```lean
OrdvecFormalization.exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
```

Cost-sensitive primary theorem:

```lean
OrdvecFormalization.exists_uniformBitmapOverlapTail_finiteCostedBayesRisk_le_and_hypergeomTail
```

General positive-base theorem:

```lean
OrdvecFormalization.exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
```

Core FNCH overlap theorem:

```lean
OrdvecFormalization.overlapNull_threshold_bayesRisk_optimal_of_lt
OrdvecFormalization.fnch_overlap_threshold_bayes_optimal
```

Cost-sensitive extension:

```lean
OrdvecFormalization.overlapNull_costed_threshold_bayesRisk_optimal_of_lt
OrdvecFormalization.fnch_overlap_costed_threshold_bayes_optimal
```

Exact constant-weight bitmap null:

```lean
OrdvecFormalization.card_bitmapOverlapFiber_of_query_card
OrdvecFormalization.bitmapOverlapTailMass_eq_bitmapHypergeomTail_of_query_card
OrdvecFormalization.bitmapUniformPMF_overlapFiber_prob
OrdvecFormalization.bitmapUniformPMF_overlapTail_prob
```

Quotient-to-threshold sufficiency bridge:

```lean
OrdvecFormalization.exists_orderedQuotientThreshold_finiteWeightedRisk_le_of_orderedEvidenceFactor
OrdvecFormalization.exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_likelihoodRatioFactor
OrdvecFormalization.exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_canonicalTilt
OrdvecFormalization.exists_overlapQuotientThreshold_finiteBayesRisk_le_of_canonicalTilt_of_lt
OrdvecFormalization.exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
```

The primary theorem quantifies over all deterministic admission sets on the
finite `K`-active bitmap space and produces a literal overlap-tail event with
Bayes risk no larger than any of them.

The cost-sensitive version also quantifies over false-accept and false-reject
costs, so asymmetric admission tradeoffs do not have to be smuggled into the
prior.

The reviewer-facing theorem map is in
[`docs/theorem-map.md`](docs/theorem-map.md).

A shorter guided read for reviewers and builders is in
[`docs/reviewer-brief.md`](docs/reviewer-brief.md).

## Proof Spine

- `FiniteExperiment.lean`: arbitrary finite statistical experiments, quotient
  pullbacks, and a quotient-form optimality theorem when Bayes evidence or the
  likelihood ratio factors through a quotient. It also includes a finite witness
  that a quotient can be sufficient for one decision target without being
  complete for a second target.
- `OrdinalSufficiency.lean`: composes quotient factorization with ordered
  evidence. If the full likelihood ratio is a monotone function of ordered
  quotient evidence, then a pulled-back ordinal threshold is Bayes-optimal among
  all deterministic full-space rules.
- `OverlapSufficiency.lean`: specializes the quotient bridge to actual overlap
  coordinates, proving that monotone likelihood-ratio factorization through
  ordinal overlap evidence yields a Bayes-optimal pulled-back actual-overlap
  threshold.
- `CanonicalTilt.lean`: instantiates the factorization contract with a finite
  exponential family over arbitrary full observations. Tilting a positive base
  law by quotient-level overlap evidence makes the likelihood ratio a monotone
  function of that evidence, so the overlap threshold theorem applies.
- `OverlapBayesOptimal.lean`: finite Bayes-risk and cost-sensitive wrappers for
  the canonical overlap-tilt threshold theorem.
- `BitmapCalibration.lean`: connects the canonical overlap-tilt theorem to the
  exact constant-weight bitmap null. The same produced actual-overlap cutoff is
  Bayes-optimal under the canonical signal model and has a hypergeometric
  upper-tail probability under the uniform `K`-active bitmap null. It also
  specializes the full observation space to the `K`-active bitmap subtype and
  proves the Bayes-optimal pulled-back threshold is exactly the literal bitmap
  overlap tail event.
- `FiniteDecision.lean`: monotone predicates on `Fin (n + 1)` are thresholds.
- `MLR.lean`: cross-multiplication MLR makes weighted Bayes admit predicates
  monotone and connects admission to a likelihood-ratio cutoff.
- `BayesThreshold.lean`: Bayes and cost-sensitive Bayes thresholds minimize
  finite pointwise risk.
- `ExponentialTilt.lean`: positive finite exponential tilts have MLR.
- `FNCH.lean`: literal actual-overlap FNCH weights match the shifted tilt after
  normalization.
- `OverlapNull.lean`: overlap-null theorem wrappers and compatibility aliases.
- `BitmapNull.lean`: constant-weight bitmap spaces, overlap fibers, and
  the exact hypergeometric point-mass and upper-tail probability theorem under
  the uniform finite bitmap law.
- `Verify.lean`: public-name checks and axiom audit.

Expected axiom baseline:

```text
[propext, Classical.choice, Quot.sound]
```

## Scope

This proves an optimality theorem for the admission rule under the stated finite
model, a quotient-form optimality theorem under explicit factorization assumptions, and
the exact constant-weight bitmap overlap null. It does not prove that real
encoders satisfy the quotient/factorization contract, it does not prove that the
textbook hypergeometric is the deployment null for real embeddings, and it does
not include randomized tests, Neyman-Pearson, UMP, Karlin-Rubin, or empirical
null calibration. It also does not claim ordinal quotients preserve all useful
semantic or computational information.

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
