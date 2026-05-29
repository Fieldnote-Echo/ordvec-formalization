# Theorem Map

This document maps the checked Lean theorem surface. It is deliberately narrow:
the formalization proves finite Bayes decision theorems, a quotient-form
optimality theorem, a canonical overlap-tilt signal instantiation, a
group-theoretic bitmap-overlap invariant theorem, a supplied calibrated-evidence
wrapper, and an exact constant-weight bitmap null.

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
OrdvecFormalization.exists_calibratedOrderedThreshold_finiteBayesRisk_le_of_orderedEvidenceFactor
OrdvecFormalization.exists_calibratedOrderedThreshold_finiteCostedBayesRisk_le_of_orderedEvidenceFactor
OrdvecFormalization.exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_likelihoodRatioFactor
OrdvecFormalization.exists_overlapQuotientThreshold_finiteWeightedRisk_le_of_canonicalTilt
OrdvecFormalization.exists_overlapQuotientThreshold_finiteBayesRisk_le_of_canonicalTilt_of_lt
OrdvecFormalization.exists_overlapQuotientThreshold_finiteBayesRisk_le_and_bitmapHypergeomTail
OrdvecFormalization.constantWeightBitmapOverlapTailCalibration
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
BitmapSymmetry
  -> overlap is the query-stabilizer orbit classifier

FiniteExperiment
  -> FiniteBayesRisk
  -> OrdinalSufficiency / OverlapSufficiency
  -> CanonicalTilt / OverlapBayesOptimal

FiniteBayesRisk + OrdinalSufficiency
  -> CalibratedEvidence

BitmapNull
  -> BitmapIncidence

CalibratedEvidence + BitmapIncidence + OverlapBayesOptimal
  -> BitmapCalibration
  -> exact hypergeometric null calibration
```

For the module-by-module proof narrative, see [`proof-spine.md`](proof-spine.md).

## Public Names

This section is the stable public theorem-name surface. Renames should be
deliberate, documented changes because downstream docs and papers cite these
names.

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
- `OrderedTailCalibration`
- `exists_calibratedOrderedThreshold_finiteBayesRisk_le_of_orderedEvidenceFactor`
- `exists_calibratedOrderedThreshold_finiteCostedBayesRisk_le_of_orderedEvidenceFactor`
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
- `BitmapCut`
- `bitmapCutThreshold`
- `ConstantWeightBitmap`
- `constantWeightBitmapUniformLaw`
- `constantWeightBitmapOverlapTailSet`
- `constantWeightBitmapOverlapEvidence`
- `overlapQuotientThresholdSet_constantWeightBitmapOverlapEvidence_eq`
- `constantWeightBitmapOverlapTailCalibration`
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
- `CalibratedEvidence.lean` packages a supplied equality at the cutoff returned
  by the ordered Bayes-optimality theorem. It does not prove null adequacy,
  event equivalence, or any real-corpus calibration claim.
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
make check-doc-names
make audit
make lint
```

`make verify` checks the public theorem dashboard and prints the axiom audit.
`make check-doc-names` extracts documented names from the markdown files and
checks that they resolve through Lean. Expected axioms are Lean's standard
baseline:

```text
[propext, Classical.choice, Quot.sound]
```
