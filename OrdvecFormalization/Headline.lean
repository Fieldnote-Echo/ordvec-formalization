/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import OrdvecFormalization.CanonicalTilt

open scoped NNReal

namespace OrdvecFormalization

/-!
# Paper-facing headline theorems

This file packages the quotient, overlap, and canonical tilt layers into theorem
names that read like the paper claim.  The proofs are intentionally thin: the
mathematical work lives in `FiniteExperiment`, `OrdinalSufficiency`,
`OverlapSufficiency`, and `CanonicalTilt`.
-/

/-- Finite Bayes risk for arbitrary full observations. -/
noncomputable def finiteBayesRisk {Ω : Type} [Fintype Ω] (p0 p1 : FiniteLaw Ω)
    (prior : Prior) (R : Set Ω) : ℝ≥0 :=
  finiteWeightedRisk p0 p1 prior.compl prior.prob R

/-- Finite cost-sensitive Bayes risk for arbitrary full observations. -/
noncomputable def finiteCostedBayesRisk {Ω : Type} [Fintype Ω] (p0 p1 : FiniteLaw Ω)
    (prior : Prior) (costs : DecisionCosts) (R : Set Ω) : ℝ≥0 :=
  finiteWeightedRisk p0 p1 (costs.falseAccept * prior.compl)
    (costs.falseReject * prior.prob) R

/--
Headline theorem, Bayes-prior form.

Under the canonical finite model where relevance tilts a positive full-space
base law by ordinal overlap evidence, an actual-overlap threshold pulled back
through the ordinal quotient is Bayes-optimal among all deterministic full-space
rules.
-/
theorem ordinal_retrieval_sufficient_for_canonical_overlap_tilt
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (base : FiniteLaw Ω) (Q : Ω → Ωq) (O : Ωq → p.support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (prior : Prior) (hprior : 0 < prior.prob) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior (overlapQuotientThresholdSet p Q O cut) ≤
        finiteBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior R := by
  simpa [finiteBayesRisk] using
    canonical_overlap_tilt_threshold_bayes_optimal p base Q O hθ prior.compl prior.prob hprior

/-- Strict-signal version of the headline Bayes-prior theorem. -/
theorem ordinal_retrieval_sufficient_for_canonical_overlap_tilt_of_lt
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (base : FiniteLaw Ω) (Q : Ω → Ωq) (O : Ωq → p.support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (hprior : 0 < prior.prob) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior (overlapQuotientThresholdSet p Q O cut) ≤
        finiteBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior R :=
  ordinal_retrieval_sufficient_for_canonical_overlap_tilt p base Q O hθ.le prior hprior

/--
Headline theorem, cost-sensitive form.

Changing priors or asymmetric costs changes only the threshold, not the
decision-rule form, provided the false-reject side has positive weight.
-/
theorem ordinal_retrieval_sufficient_for_canonical_overlap_tilt_costed
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (base : FiniteLaw Ω) (Q : Ω → Ωq) (O : Ωq → p.support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteCostedBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior costs (overlapQuotientThresholdSet p Q O cut) ≤
        finiteCostedBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior costs R := by
  simpa [finiteCostedBayesRisk] using
    canonical_overlap_tilt_threshold_bayes_optimal p base Q O hθ
      (costs.falseAccept * prior.compl) (costs.falseReject * prior.prob) hw1

/-- Strict-signal version of the cost-sensitive headline theorem. -/
theorem ordinal_retrieval_sufficient_for_canonical_overlap_tilt_costed_of_lt
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (base : FiniteLaw Ω) (Q : Ω → Ωq) (O : Ωq → p.support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteCostedBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior costs (overlapQuotientThresholdSet p Q O cut) ≤
        finiteCostedBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior costs R :=
  ordinal_retrieval_sufficient_for_canonical_overlap_tilt_costed
    p base Q O hθ.le prior costs hw1

/--
Paper-language alias for the main conditional claim.

Ordinal overlap evidence is retrieval-sufficient, in the finite Bayes sense,
under the canonical overlap-tilt model.
-/
theorem ordvec_headline_theorem
    {Ω Ωq : Type} [Fintype Ω]
    (p : FNCHParams) (base : FiniteLaw Ω) (Q : Ω → Ωq) (O : Ωq → p.support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (hprior : 0 < prior.prob) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set Ω,
      finiteBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior (overlapQuotientThresholdSet p Q O cut) ≤
        finiteBayesRisk
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
          (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
          prior R :=
  ordinal_retrieval_sufficient_for_canonical_overlap_tilt_of_lt
    p base Q O hθ prior hprior

end OrdvecFormalization
