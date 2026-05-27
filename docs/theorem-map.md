# Theorem Map

This document maps the reviewer-facing claim to the checked Lean theorem
surface. It is deliberately narrower than the OrdVec paper narrative: the
formalization proves finite Bayes decision theorems, a representation-free
quotient no-loss theorem, a canonical overlap-tilt signal instantiation, and an
exact constant-composition bitmap null.

## Citation Claim

For `K`-active bitmap documents in dimension `D`, under the canonical finite
overlap-tilt signal model with uniform bitmap null and signal parameter
`0 < theta`, literal overlap-tail retrieval is Bayes-optimal among all
deterministic bitmap-document admission rules. The same threshold event has
exactly the hypergeometric upper-tail probability under the model null.

Checked theorem:

```lean
OrdvecFormalization.ordvec_bitmap_uniform_null_headline_theorem
```

Cost-sensitive checked theorem:

```lean
OrdvecFormalization.ordvec_bitmap_uniform_null_costed_headline_theorem
```

General positive-base theorem, with separate uniform-null tail calibration at
the same cutoff:

```lean
OrdvecFormalization.ordvec_bitmap_headline_theorem
```

## Supporting Layers

Core FNCH overlap theorem:

```lean
OrdvecFormalization.overlapNull_threshold_isBayesOptimal
OrdvecFormalization.fnch_overlap_threshold_bayes_optimal
```

Cost-sensitive extension:

```lean
OrdvecFormalization.overlapNull_costed_threshold_isBayesOptimal
OrdvecFormalization.fnch_overlap_costed_threshold_bayes_optimal
```

Exact constant-composition bitmap null:

```lean
OrdvecFormalization.card_bitmapOverlapFiber_of_query_card
OrdvecFormalization.bitmapFalsePositiveRate_eq_bitmapHypergeomTail_of_query_card
OrdvecFormalization.bitmapUniformPMF_overlapFiber_prob
OrdvecFormalization.bitmapUniformPMF_overlapTail_prob
```

Quotient sufficiency layer:

```lean
OrdvecFormalization.quotient_bayes_no_loss
OrdvecFormalization.quotient_bayes_no_loss_of_likelihoodRatioFactorsThrough
OrdvecFormalization.orderedQuotient_threshold_no_loss_of_orderedEvidenceFactor
OrdvecFormalization.ordinal_overlap_threshold_bayes_optimal_of_likelihoodRatioFactor
OrdvecFormalization.canonical_overlap_tilt_threshold_bayes_optimal
OrdvecFormalization.ordvec_headline_theorem
OrdvecFormalization.ordvec_headline_theorem_with_bitmap_null
OrdvecFormalization.bitmap_doc_tail_bayes_optimal_with_null
OrdvecFormalization.ordvec_bitmap_headline_theorem
OrdvecFormalization.ordvec_bitmap_uniform_null_headline_theorem
OrdvecFormalization.denseToy_retrieval_sufficient_not_representation_complete
```

The legacy FNCH theorem quantifies over:

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

BitmapCalibration
  -> ordvec_bitmap_uniform_null_headline_theorem
```

## Proof Spine

1. `FiniteExperiment.lean`
   This is the representation-free finite statistical experiment layer. It
   defines arbitrary finite positive laws, finite weighted risk, quotient
   pullbacks, and proves `quotient_bayes_no_loss`: if pointwise Bayes evidence
   is constant on quotient fibers, then some quotient-form admit set has no
   larger risk than any full-space admit set. The theorem
   `quotient_bayes_no_loss_of_likelihoodRatioFactorsThrough` gives the
   likelihood-ratio version: if the full likelihood ratio factors through a
   quotient map, then positive reject-side weights admit a Bayes-optimal
   quotient-form rule. The deterministic toy theorem
   `denseToy_retrieval_sufficient_not_representation_complete` witnesses the
   intended boundary: a quotient can be sufficient for a retrieval target while
   failing to preserve a second target that varies inside quotient fibers.

2. `OrdinalSufficiency.lean`
   This composes the quotient layer with ordered evidence. It defines
   `orderedQuotientThresholdSet`, an evidence threshold pulled back through a
   quotient map, and proves
   `orderedQuotient_threshold_no_loss_of_orderedEvidenceFactor`: if the full
   likelihood ratio is a monotone function of ordered quotient evidence, then
   some pulled-back ordinal threshold has no larger weighted Bayes risk than any
   deterministic full-space admit set.

3. `OverlapSufficiency.lean`
   This specializes the previous theorem to actual-overlap coordinates. It
   defines `overlapQuotientThresholdSet`, proves it is the same pulled-back set
   as `orderedQuotientThresholdSet`, and exposes
   `ordinal_overlap_threshold_bayes_optimal_of_likelihoodRatioFactor`: if the
   dense/full likelihood ratio factors monotonically through quotient-level
   overlap evidence, then an actual-overlap threshold is Bayes-optimal among all
   deterministic full-space rules.

4. `CanonicalTilt.lean`
   This instantiates the factorization contract with a canonical finite
   exponential family over arbitrary full observations. It defines
   `finiteExponentialTilt`, proves
   `finiteLikelihoodRatio_finiteExponentialTilt_eq_factor`, and packages the
   result as `canonical_overlap_tilt_threshold_bayes_optimal`: if a positive
   full-space base law is tilted by quotient-level overlap evidence, then the
   resulting likelihood ratio factors monotonically through that evidence, so a
   pulled-back actual-overlap threshold is Bayes-optimal among all deterministic
   full-space rules.

5. `Headline.lean`
   This is the paper-facing wrapper. It defines generic full-observation
   `finiteBayesRisk` and `finiteCostedBayesRisk`, then exposes
   `ordinal_retrieval_sufficient_for_canonical_overlap_tilt`,
   `ordinal_retrieval_sufficient_for_canonical_overlap_tilt_costed`, and
   `ordvec_headline_theorem`. The headline theorem is the strict-signal,
   Bayes-prior version: under the canonical overlap-tilt model, ordinal overlap
   evidence is retrieval-sufficient in the sense that a pulled-back
   actual-overlap threshold is optimal among all deterministic full-space rules.

6. `BitmapCalibration.lean`
   This connects the canonical overlap-tilt headline theorem to the exact
   constant-composition bitmap null. It builds the FNCH overlap parameters for
   two `K`-active bitmaps in dimension `D`, obtains the Bayes-optimal
   actual-overlap cutoff from the canonical signal theorem, and proves that the
   uniform bitmap null assigns the corresponding threshold event exactly the
   hypergeometric upper-tail probability. The theorem
   `ordvec_headline_theorem_with_bitmap_null` is the checked "optimal under the
   signal model, tail-calibrated under the bitmap null" bridge. The more
   concrete theorem `bitmap_doc_tail_bayes_optimal_with_null` specializes the
   full observation space to the `K`-active bitmap document subtype and proves
   that the Bayes-optimal pulled-back threshold set is exactly the literal
   bitmap overlap tail event. The paper-facing aliases
   `ordvec_bitmap_headline_theorem` and
   `ordvec_bitmap_costed_headline_theorem` expose this final surface.

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
   `overlapNull_threshold_isBayesOptimal` is the core FNCH overlap theorem. The
   final aliases in that file keep paper-language names available without
   duplicating the proof.

13. `BitmapNull.lean`
   This gives the independent exact-null route for constant-composition bitmap
   candidate generation. It defines `bitmapSpace`, overlap fibers, tail events,
   and the structured inside/outside choice space whose cardinality is the
   hypergeometric numerator. The main counting theorem
   `card_bitmapOverlapFiber_of_query_card` proves the overlap-fiber cardinality,
   and `bitmapFalsePositiveRate_eq_bitmapHypergeomTail_of_query_card` identifies
   the threshold-event cardinal ratio with the closed-form hypergeometric upper
   tail. The `bitmapUniformPMF_*` theorems package the same statements as
   probabilities under the uniform `PMF` over `K`-active document bitmaps.

## Public Names

Core theorem names:

- `finiteWeightedBayesAdmitSet_optimal`
- `mem_quotientPullback_of_quotient_preserving`
- `quotientBayesAdmitSet_pullback_eq`
- `quotient_bayes_no_loss`
- `finiteWeightedBayesAdmit_iff_cutoff_le_likelihoodRatio`
- `finiteBayesAdmitFactorsThrough_of_likelihoodRatioFactorsThrough`
- `quotient_bayes_no_loss_of_likelihoodRatioFactorsThrough`
- `orderedQuotientThresholdSet`
- `FiniteLikelihoodRatioFactorsThroughOrderedEvidence`
- `orderedQuotient_threshold_no_loss_of_monotone_likelihoodRatioFactor`
- `orderedQuotient_threshold_no_loss_of_orderedEvidenceFactor`
- `overlapQuotientThresholdSet`
- `overlapQuotientThresholdSet_eq_orderedQuotientThresholdSet`
- `FiniteLikelihoodRatioFactorsThroughOverlapEvidence`
- `overlapQuotient_threshold_no_loss_of_overlapEvidenceFactor`
- `ordinal_overlap_threshold_bayes_optimal_of_likelihoodRatioFactor`
- `finiteExponentialTilt`
- `finiteLikelihoodRatio_finiteExponentialTilt_eq_factor`
- `finiteExponentialTilt_likelihoodRatioFactorsThroughOrderedEvidence`
- `finiteExponentialTilt_likelihoodRatioFactorsThroughOverlapEvidence`
- `overlapQuotient_threshold_no_loss_of_finiteExponentialTilt`
- `canonical_overlap_tilt_threshold_bayes_optimal`
- `finiteBayesRisk`
- `finiteCostedBayesRisk`
- `ordinal_retrieval_sufficient_for_canonical_overlap_tilt`
- `ordinal_retrieval_sufficient_for_canonical_overlap_tilt_costed`
- `ordvec_headline_theorem`
- `bitmapFNCHParams`
- `BitmapDoc`
- `bitmapDocOverlapTailSet`
- `bitmapDocOverlapEvidence`
- `overlapQuotientThresholdSet_bitmapDocOverlapEvidence_eq`
- `ordvec_headline_theorem_with_bitmap_null`
- `ordvec_headline_costed_theorem_with_bitmap_null`
- `bitmap_doc_tail_bayes_optimal_with_null`
- `bitmap_doc_tail_costed_bayes_optimal_with_null`
- `ordvec_bitmap_headline_theorem`
- `ordvec_bitmap_costed_headline_theorem`
- `ordvec_bitmap_uniform_null_headline_theorem`
- `ordvec_bitmap_uniform_null_costed_headline_theorem`
- `denseToy_retrievalTarget_factorsThrough`
- `denseToy_transformationTarget_not_factorsThrough`
- `denseToy_retrieval_sufficient_not_representation_complete`
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
- `overlapNull_threshold_isBayesOptimal`
- `overlapNull_costed_threshold_isBayesOptimal`
- `card_bitmapSpace`
- `card_insideOutsideChoices_of_query_card`
- `card_bitmapOverlapFiber_of_query_card`
- `bitmapHypergeomMass_eq_insideOutsideChoices_card_ratio`
- `bitmapHypergeomMass_eq_overlapFiber_card_ratio`
- `card_bitmapOverlapTailEvent_eq_sum_overlapFiber_card_of_query_card`
- `bitmapFalsePositiveRate_eq_bitmapHypergeomTail_of_query_card`
- `bitmapUniformPMF`
- `bitmapUniformPMF_overlapFiber_prob`
- `bitmapUniformPMF_overlapTail_prob`

Paper-language aliases:

- `ordvec_bitmap_headline_theorem`
- `ordvec_bitmap_costed_headline_theorem`
- `ordvec_bitmap_uniform_null_headline_theorem`
- `ordvec_bitmap_uniform_null_costed_headline_theorem`
- `literal_fnch_overlap_has_mlr`
- `fnch_overlap_admit_threshold`
- `fnch_overlap_threshold_bayes_optimal`
- `fnch_overlap_costed_threshold_bayes_optimal`

## What Is Not Claimed

- No empirical null calibration theorem is formalized here. The new bitmap-null
  route concerns the exact idealized constant-composition null, not real-corpus
  independence or effective dimension.
- No claim is made that the textbook hypergeometric is the deployment null for
  real embeddings.
- No claim is made that a real encoder's semantic evidence actually factors
  through an ordinal quotient; the quotient theorem states the exact sufficient
  condition under which such compression is decision-theoretically lossless.
- No claim is made that retrieval sufficiency makes the quotient
  representation-complete. The checked toy witness shows a quotient can preserve
  one target while provably discarding another.
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
