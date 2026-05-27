# Theorem Map

This document maps the checked Lean theorem surface. It is deliberately narrow:
the formalization proves finite Bayes decision theorems, a quotient-form
optimality theorem, a canonical overlap-tilt signal instantiation, a
group-theoretic bitmap-overlap invariant theorem, and an exact constant-weight
bitmap null.

## Main Claim

For `K`-active bitmaps in dimension `D`, under the canonical finite
overlap-tilt signal model with uniform bitmap null and signal parameter
`0 < theta`, a literal overlap-tail rule is Bayes-optimal among all
deterministic admission rules on the constant-weight bitmap observation space.
The same threshold event has exactly the hypergeometric upper-tail probability
under the model null.

Checked theorem:

```lean
OrdvecFormalization.exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
```

Cost-sensitive checked theorem:

```lean
OrdvecFormalization.exists_uniformBitmapOverlapTail_finiteCostedBayesRisk_le_and_hypergeomTail
```

General positive-base theorem, with separate uniform-null tail calibration at
the same cutoff:

```lean
OrdvecFormalization.exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
```

## Supporting Layers

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

Bitmap symmetry layer:

```lean
OrdvecFormalization.bitmapOverlap_queryStabilizer_eq
OrdvecFormalization.exists_queryStabilizer_permuteBitmap_eq_of_card_eq_overlap_eq
OrdvecFormalization.exists_queryStabilizer_permuteBitmap_eq_iff_overlap_eq_of_card_eq
OrdvecFormalization.invariantOn_constantWeightBitmapSpace_factorsThrough_overlap
```

Quotient sufficiency layer:

```lean
OrdvecFormalization.exists_quotientPullback_finiteWeightedRisk_le
OrdvecFormalization.exists_quotientPullback_finiteWeightedRisk_le_of_likelihoodRatioFactorsThrough
OrdvecFormalization.exists_orderedQuotientThreshold_finiteWeightedRisk_le_of_orderedEvidenceFactor
OrdvecFormalization.exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_likelihoodRatioFactor
OrdvecFormalization.exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_canonicalTilt
OrdvecFormalization.exists_overlapQuotientThreshold_finiteBayesRisk_le_of_canonicalTilt_of_lt
OrdvecFormalization.exists_overlapQuotientThreshold_finiteBayesRisk_le_and_bitmapHypergeomTail
OrdvecFormalization.exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
OrdvecFormalization.exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
OrdvecFormalization.quotientFiberExample_quotientTarget_factorsThrough_not_fiberTarget
```

The core overlap-null theorem quantifies over:

- `p : FNCHParams`, carrying `k <= N` and `draws <= N`.
- `theta0 theta1 : Real`, with strict hypothesis `theta0 < theta1`.
- `prior : Prior`, a bundled prior probability for `H1`.
- all deterministic admission sets `R : Set p.support`.

It produces a cut `cut : Fin (p.hi - p.lo + 2)` such that the
actual-overlap threshold set has Bayes risk no larger than any deterministic
admission set.

The cost-sensitive theorem additionally quantifies over
`costs : DecisionCosts`, whose `falseAccept` and `falseReject` fields weight the
two error types independently.

## Dependency Shape

```text
FiniteExperiment
  -> OrdinalSufficiency / OverlapSufficiency
  -> CanonicalTilt
  -> BitmapCalibration

BitmapNull
  -> BitmapCalibration
  -> BitmapSymmetry

BitmapCalibration
  -> exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail

BitmapSymmetry
  -> invariantOn_constantWeightBitmapSpace_factorsThrough_overlap
```

## Proof Spine

1. `FiniteExperiment.lean`
   This is the finite quotient decision layer. It
   defines arbitrary finite positive laws, finite weighted risk, quotient
   pullbacks, and proves `exists_quotientPullback_finiteWeightedRisk_le`: if pointwise Bayes evidence
   is constant on quotient fibers, then some quotient-form admit set has no
   larger risk than any full-space admit set. The theorem
   `exists_quotientPullback_finiteWeightedRisk_le_of_likelihoodRatioFactorsThrough` gives the
   likelihood-ratio version: if the full likelihood ratio factors through a
   quotient map, then positive reject-side weights admit a Bayes-optimal
   quotient-form rule. The finite example theorem
   `quotientFiberExample_quotientTarget_factorsThrough_not_fiberTarget` witnesses the
   intended boundary: a quotient can be sufficient for one decision target while
   failing to preserve a second target that varies inside quotient fibers.

2. `OrdinalSufficiency.lean`
   This composes the quotient layer with ordered evidence. It defines
   `orderedQuotientThresholdSet`, an evidence threshold pulled back through a
   quotient map, and proves
   `exists_orderedQuotientThreshold_finiteWeightedRisk_le_of_orderedEvidenceFactor`: if the full
   likelihood ratio is a monotone function of ordered quotient evidence, then
   some pulled-back ordinal threshold has no larger weighted Bayes risk than any
   deterministic full-space admit set.

3. `OverlapSufficiency.lean`
   This specializes the previous theorem to actual-overlap coordinates. It
   defines `overlapQuotientThresholdSet`, proves it is the same pulled-back set
   as `orderedQuotientThresholdSet`, and exposes
   `exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_likelihoodRatioFactor`: if the
   full likelihood ratio factors monotonically through quotient-level
   overlap evidence, then an actual-overlap threshold is Bayes-optimal among all
   deterministic full-space rules.

4. `CanonicalTilt.lean`
   This instantiates the factorization contract with a canonical finite
   exponential family over arbitrary full observations. It defines
   `finiteExponentialTilt`, proves
   `finiteLikelihoodRatio_finiteExponentialTilt_eq_factor`, and packages the
   result as `exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_canonicalTilt`: if a positive
   full-space base law is tilted by quotient-level overlap evidence, then the
   resulting likelihood ratio factors monotonically through that evidence, so a
   pulled-back actual-overlap threshold is Bayes-optimal among all deterministic
   full-space rules.

5. `OverlapBayesOptimal.lean`
   This is the finite Bayes-risk wrapper. It defines generic full-observation
   `finiteBayesRisk` and `finiteCostedBayesRisk`, then exposes
   `exists_overlapQuotientThreshold_finiteBayesRisk_le_of_canonicalTilt`,
   `exists_overlapQuotientThreshold_finiteCostedBayesRisk_le_of_canonicalTilt`, and
   `exists_overlapQuotientThreshold_finiteBayesRisk_le_of_canonicalTilt_of_lt`.
   The strict cost-sensitive wrapper is
   `exists_overlapQuotientThreshold_finiteCostedBayesRisk_le_of_canonicalTilt_of_lt`.
   The strict-parameter version says that, under the canonical overlap-tilt
   model, a pulled-back actual-overlap threshold is optimal among all
   deterministic full-space rules.

6. `BitmapCalibration.lean`
   This connects the canonical overlap-tilt theorem to the exact
   constant-weight bitmap null. It builds the FNCH overlap parameters for
   two `K`-active bitmaps in dimension `D`, obtains the Bayes-optimal
   actual-overlap cutoff from the canonical signal theorem, and proves that the
   uniform bitmap null assigns the corresponding threshold event exactly the
   hypergeometric upper-tail probability. The theorem
   `exists_overlapQuotientThreshold_finiteBayesRisk_le_and_bitmapHypergeomTail`
   is the checked "optimal under the signal model, tail-calibrated under the
   bitmap null" bridge. The concrete theorem
   `exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail`
   specializes the full observation space to the `K`-active bitmap subtype and
   proves that the Bayes-optimal pulled-back threshold set is exactly the
   literal bitmap overlap tail event.

7. `FiniteDecision.lean`
   `exists_threshold_of_monotone_pred` proves that every monotone predicate on
   `Fin (n + 1)` is represented by a threshold cut in `Fin (n + 2)`. The two
   extra boundary cuts encode accept-all and reject-all rules.

8. `MLR.lean`
   `HasMLR` states monotone likelihood ratio by cross multiplication:
   `p1 x * p0 y <= p1 y * p0 x` for `x <= y`.
   `mlr_monotone_weightedBayesAdmit` proves that this makes any weighted
   pointwise Bayes admit predicate monotone. Positivity of `p0.mass x` is used
   exactly at the final cancellation step. The theorem
   `bayesAdmit_iff_priorOddsCutoff_le_likelihoodRatio` connects the
   cross-multiplied statement to the usual likelihood-ratio cutoff. The cutoff
   constants themselves carry the positive-denominator witness, so degenerate
   zero-`H1` or zero reject-side weight cases are not given an odds-threshold
   interpretation by the API.

9. `BayesThreshold.lean`
   `bayesAdmit_isThreshold` turns monotone Bayes admission into a threshold.
   `threshold_bayesRisk_optimal` proves optimality by `Finset.sum_le_sum`,
   since finite Bayes risk decomposes pointwise over support points.
   `costed_threshold_bayesRisk_optimal` gives the same result with independent
   false-accept and false-reject costs.

10. `ExponentialTilt.lean`
   `exponentialTilt_hasMLR` proves that positive finite base weights tilted by
   `exp (theta * x)` have MLR as `theta` increases.

11. `FNCH.lean`
   `fnchActualPMF_mass_eq_fnchPMF_mass` connects literal actual-overlap FNCH
   weights
   `choose k x * choose (N-k) (draws-x) * exp(theta*x)`
   to the shifted exponential-tilt implementation after normalization.
   `fnchActual_actualOverlapThreshold_bayesRisk_optimal_of_lt` gives the
   strict-parameter FNCH threshold optimality theorem.

12. `OverlapNull.lean`
   `overlapNull_threshold_bayesRisk_optimal_of_lt` is the core FNCH overlap theorem. The
   final aliases in that file keep compatibility names available without
   duplicating the proof.

13. `BitmapNull.lean`
   This gives the independent exact-null route for constant-weight bitmap
   overlap. It defines `constantWeightBitmapSpace`, overlap fibers, tail events,
   and the structured inside/outside choice space whose cardinality is the
   hypergeometric numerator. The main counting theorem
   `card_bitmapOverlapFiber_of_query_card` proves the overlap-fiber cardinality,
   and `bitmapOverlapTailMass_eq_bitmapHypergeomTail_of_query_card` identifies
   the threshold-event cardinal ratio with the closed-form hypergeometric upper
   tail. The `bitmapUniformPMF_*` theorems package the same statements as
   probabilities under the uniform `PMF` over `K`-active bitmaps.

14. `BitmapSymmetry.lean`
   This gives the group-theoretic explanation for the bitmap quotient. It
   defines the coordinate permutation group and query stabilizer, proves that
   query-stabilizer permutations preserve literal overlap, constructs a
   query-stabilizer permutation between any two equal-cardinality bitmaps with
   the same query overlap, and packages the maximal-invariant consequence:
   every query-stabilizer-invariant statistic on the constant-weight bitmap
   space factors through literal overlap.

## Public Names

Core theorem names:

- `finiteWeightedBayesAdmitSet_optimal`
- `mem_quotientPullback_of_quotient_preserving`
- `quotientBayesAdmitSet_pullback_eq`
- `exists_quotientPullback_finiteWeightedRisk_le`
- `finiteWeightedBayesAdmit_iff_cutoff_le_likelihoodRatio`
- `finiteBayesAdmitFactorsThrough_of_likelihoodRatioFactorsThrough`
- `exists_quotientPullback_finiteWeightedRisk_le_of_likelihoodRatioFactorsThrough`
- `orderedQuotientThresholdSet`
- `FiniteLikelihoodRatioFactorsThroughOrderedEvidence`
- `exists_orderedQuotientThreshold_finiteWeightedRisk_le_of_monotone`
- `exists_orderedQuotientThreshold_finiteWeightedRisk_le_of_orderedEvidenceFactor`
- `overlapQuotientThresholdSet`
- `overlapQuotientThresholdSet_eq_orderedQuotientThresholdSet`
- `FiniteLikelihoodRatioFactorsThroughOverlapEvidence`
- `exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_overlapEvidenceFactor`
- `exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_likelihoodRatioFactor`
- `finiteExponentialTilt`
- `finiteLikelihoodRatio_finiteExponentialTilt_eq_factor`
- `finiteExponentialTilt_likelihoodRatioFactorsThroughOrderedEvidence`
- `finiteExponentialTilt_likelihoodRatioFactorsThroughOverlapEvidence`
- `exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_finiteExponentialTilt`
- `exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_canonicalTilt`
- `finiteBayesRisk`
- `finiteCostedBayesRisk`
- `exists_overlapQuotientThreshold_finiteBayesRisk_le_of_canonicalTilt`
- `exists_overlapQuotientThreshold_finiteCostedBayesRisk_le_of_canonicalTilt`
- `exists_overlapQuotientThreshold_finiteBayesRisk_le_of_canonicalTilt_of_lt`
- `exists_overlapQuotientThreshold_finiteCostedBayesRisk_le_of_canonicalTilt_of_lt`
- `bitmapOverlapParams`
- `ConstantWeightBitmap`
- `constantWeightBitmapOverlapTailSet`
- `constantWeightBitmapOverlapEvidence`
- `overlapQuotientThresholdSet_constantWeightBitmapOverlapEvidence_eq`
- `exists_overlapQuotientThreshold_finiteBayesRisk_le_and_bitmapHypergeomTail`
- `exists_overlapQuotientThreshold_finiteCostedBayesRisk_le_and_bitmapHypergeomTail`
- `exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail`
- `exists_constantWeightBitmapOverlapTail_finiteCostedBayesRisk_le_and_hypergeomTail`
- `exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail`
- `exists_uniformBitmapOverlapTail_finiteCostedBayesRisk_le_and_hypergeomTail`
- `quotientFiberExample_quotientTarget_factorsThrough`
- `quotientFiberExample_fiberTarget_not_factorsThrough`
- `quotientFiberExample_quotientTarget_factorsThrough_not_fiberTarget`
- `mlr_monotone_weightedBayesAdmit`
- `mlr_monotone_bayesAdmit`
- `bayesAdmit_iff_priorOddsCutoff_le_likelihoodRatio`
- `weightedBayesAdmit_isThreshold`
- `bayesAdmit_isThreshold`
- `costedBayesAdmit_isThreshold`
- `weighted_threshold_bayesRisk_optimal`
- `threshold_bayesRisk_optimal`
- `costed_threshold_bayesRisk_optimal`
- `exponentialTilt_hasMLR`
- `fnchActualPMF_mass_eq_fnchPMF_mass`
- `overlapNull_threshold_bayesRisk_optimal_of_lt`
- `overlapNull_costed_threshold_bayesRisk_optimal_of_lt`
- `card_constantWeightBitmapSpace`
- `card_insideOutsideChoices_of_query_card`
- `card_bitmapOverlapFiber_of_query_card`
- `bitmapHypergeomMass_eq_insideOutsideChoices_card_ratio`
- `bitmapHypergeomMass_eq_overlapFiber_card_ratio`
- `card_bitmapOverlapTailEvent_eq_sum_overlapFiber_card_of_query_card`
- `bitmapOverlapTailMass_eq_bitmapHypergeomTail_of_query_card`
- `bitmapUniformPMF`
- `bitmapUniformPMF_overlapFiber_prob`
- `bitmapUniformPMF_overlapTail_prob`
- `BitmapPerm`
- `queryStabilizer`
- `permuteBitmap`
- `bitmapOverlap_queryStabilizer_eq`
- `exists_queryStabilizer_permuteBitmap_eq_of_card_eq_overlap_eq`
- `exists_queryStabilizer_permuteBitmap_eq_iff_overlap_eq_of_card_eq`
- `invariantOn_constantWeightBitmapSpace_eq_of_overlap_eq`
- `invariantOn_constantWeightBitmapSpace_factorsThrough_overlap`

Compatibility aliases:

- `fnchActual_overlap_hasMLR_of_lt`
- `fnch_overlap_admit_threshold`
- `fnch_overlap_threshold_bayes_optimal`
- `fnch_overlap_costed_threshold_bayes_optimal`

## What Is Not Claimed

- No empirical null calibration theorem is formalized here. The new bitmap-null
  route concerns the exact idealized constant-weight null, not real-corpus
  independence or effective dimension.
- No claim is made that the textbook hypergeometric is the deployment null for
  real embeddings.
- No claim is made that a real encoder's semantic evidence actually factors
  through an ordinal quotient; the quotient theorem states the exact sufficient
  condition under which such compression is decision-theoretically lossless.
- No claim is made that real encoders satisfy the query-stabilizer symmetry
  assumption. The symmetry theorem identifies the canonical invariant when the
  bitmap problem is treated as invariant under query-preserving coordinate
  relabelings.
- No claim is made that quotient sufficiency for one decision makes the quotient
  representation-complete. The checked finite witness shows a quotient can
  preserve one target while provably discarding another.
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
