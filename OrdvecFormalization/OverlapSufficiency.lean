/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import OrdvecFormalization.OrdinalSufficiency
import OrdvecFormalization.FNCH

open scoped NNReal

namespace OrdvecFormalization

/-!
# Overlap-facing quotient sufficiency

This file specializes the ordered quotient sufficiency theorem to actual overlap
coordinates.  The observation space is still arbitrary: a quotient map extracts
an ordinal observation, and an overlap statistic on that quotient lands in the
feasible FNCH overlap support.
-/

/-- Pull an actual-overlap threshold back through an ordinal quotient. -/
def overlapQuotientThresholdSet {Ω Ωq : Type} (p : FNCHParams)
    (Q : Ω → Ωq) (O : Ωq → p.support) (cut : Fin (p.hi - p.lo + 2)) : Set Ω :=
  {ω | O (Q ω) ∈ actualOverlapThresholdSet p cut}

/-- Actual-overlap quotient thresholds are ordered quotient thresholds. -/
theorem overlapQuotientThresholdSet_eq_orderedQuotientThresholdSet {Ω Ωq : Type}
    (p : FNCHParams) (Q : Ω → Ωq) (O : Ωq → p.support)
    (cut : Fin (p.hi - p.lo + 2)) :
    overlapQuotientThresholdSet p Q O cut =
      orderedQuotientThresholdSet Q O cut := by
  ext ω
  simp [overlapQuotientThresholdSet, orderedQuotientThresholdSet,
    actualOverlapThresholdSet_eq_thresholdSet p cut]

/--
Overlap-facing factorization condition: the full likelihood ratio is a monotone
function of the actual-overlap evidence extracted from an ordinal quotient.
-/
def FiniteLikelihoodRatioFactorsThroughOverlapEvidence {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (Q : Ω → Ωq) (O : Ωq → p.support)
    (p0 p1 : FiniteLaw Ω) : Prop :=
  FiniteLikelihoodRatioFactorsThroughOrderedEvidence Q O p0 p1

/--
If the full likelihood ratio factors monotonically through quotient-level
overlap evidence, then a pulled-back actual-overlap threshold is Bayes-optimal
among all deterministic full-space admit sets.
-/
theorem overlapQuotient_threshold_no_loss_of_overlapEvidenceFactor
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (Q : Ω → Ωq) (O : Ωq → p.support)
    (p0 p1 : FiniteLaw Ω) (w0 w1 : ℝ≥0) (hw1 : 0 < w1)
    (hfactor : FiniteLikelihoodRatioFactorsThroughOverlapEvidence p Q O p0 p1) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteWeightedRisk p0 p1 w0 w1 (overlapQuotientThresholdSet p Q O cut) ≤
        finiteWeightedRisk p0 p1 w0 w1 R := by
  rcases orderedQuotient_threshold_no_loss_of_orderedEvidenceFactor
      Q O p0 p1 w0 w1 hw1 hfactor with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro R
  simpa [overlapQuotientThresholdSet_eq_orderedQuotientThresholdSet p Q O cut] using hcut R

/--
Paper-language alias: under monotone likelihood-ratio factorization through
ordinal overlap evidence, actual-overlap threshold retrieval is Bayes-optimal
against all deterministic full-space rules.
-/
theorem ordinal_overlap_threshold_bayes_optimal_of_likelihoodRatioFactor
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (Q : Ω → Ωq) (O : Ωq → p.support)
    (p0 p1 : FiniteLaw Ω) (w0 w1 : ℝ≥0) (hw1 : 0 < w1)
    (hfactor : FiniteLikelihoodRatioFactorsThroughOverlapEvidence p Q O p0 p1) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteWeightedRisk p0 p1 w0 w1 (overlapQuotientThresholdSet p Q O cut) ≤
        finiteWeightedRisk p0 p1 w0 w1 R :=
  overlapQuotient_threshold_no_loss_of_overlapEvidenceFactor p Q O p0 p1 w0 w1 hw1 hfactor

end OrdvecFormalization
