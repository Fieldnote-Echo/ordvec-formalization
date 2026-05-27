/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import OrdvecFormalization.FNCH

open scoped NNReal

namespace OrdvecFormalization

/-!
# Overlap-null theorem surface

The first proof milestones are the finite monotone-decision theorem in
`OrdvecFormalization.BayesThreshold`, the reusable exponential-tilt MLR bridge
in `OrdvecFormalization.ExponentialTilt`, and the feasible FNCH instantiation in
`OrdvecFormalization.FNCH`.

Corpus null calibration and the broader OrdVec overlap interpretation are
deliberately kept outside this theorem surface.

The citation theorem is `overlapNull_threshold_isBayesOptimal`. The aliases at
the end of this file keep paper-language names available without duplicating the
proof spine.
-/

/-- Paper-facing name for actual-overlap threshold admission sets. -/
def overlapAdmissionThresholdSet :=
  actualOverlapThresholdSet

/-- Paper-facing FNCH MLR theorem. -/
theorem overlapNull_fnch_hasMLR (p : FNCHParams) {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) :
    HasMLR (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) :=
  fnchActual_hasMLR_of_lt p hθ

/-- Paper-facing FNCH Bayes-admit threshold theorem in actual overlap coordinates. -/
theorem overlapNull_bayesAdmit_isThreshold (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ < θ₁) (prior : Prior) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ x : p.support,
      bayesAdmit (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior x ↔
        x ∈ overlapAdmissionThresholdSet p cut :=
  fnchActual_bayesAdmit_isActualOverlapThreshold_of_lt p hθ prior

/-- Paper-facing FNCH Bayes-risk optimality theorem in actual overlap coordinates. -/
theorem overlapNull_threshold_bayesRisk_optimal (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ < θ₁) (prior : Prior) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      bayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior
          (overlapAdmissionThresholdSet p cut) ≤
        bayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior R :=
  fnchActual_actualOverlapThreshold_bayesRisk_optimal_of_lt p hθ prior

/-- Paper-facing cost-sensitive FNCH Bayes-admit threshold theorem. -/
theorem overlapNull_costed_bayesAdmit_isThreshold (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ x : p.support,
      costedBayesAdmit (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior costs x ↔
        x ∈ overlapAdmissionThresholdSet p cut :=
  fnchActual_costedBayesAdmit_isActualOverlapThreshold_of_lt p hθ prior costs

/-- Paper-facing cost-sensitive FNCH Bayes-risk optimality theorem. -/
theorem overlapNull_costed_threshold_bayesRisk_optimal (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      costedBayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior costs
          (overlapAdmissionThresholdSet p cut) ≤
        costedBayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior costs R :=
  fnchActual_costed_actualOverlapThreshold_bayesRisk_optimal_of_lt p hθ prior costs

/--
Paper-facing citation theorem.

For a literal FNCH overlap model with `θ₀ < θ₁`, the Bayes-risk-minimizing
deterministic admission rule is a threshold in the actual overlap count.
-/
theorem overlapNull_threshold_isBayesOptimal (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ < θ₁) (prior : Prior) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      bayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior
          (overlapAdmissionThresholdSet p cut) ≤
        bayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior R :=
  overlapNull_threshold_bayesRisk_optimal p hθ prior

/--
Paper-facing cost-sensitive citation theorem.

For a literal FNCH overlap model with `θ₀ < θ₁`, the cost-sensitive
Bayes-risk-minimizing deterministic admission rule is a threshold in the actual
overlap count.
-/
theorem overlapNull_costed_threshold_isBayesOptimal (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      costedBayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior costs
          (overlapAdmissionThresholdSet p cut) ≤
        costedBayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior costs R :=
  overlapNull_costed_threshold_bayesRisk_optimal p hθ prior costs

/-- Paper-language alias: literal FNCH overlap likelihood ratios are monotone. -/
theorem literal_fnch_overlap_has_mlr (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ < θ₁) :
    HasMLR (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) :=
  overlapNull_fnch_hasMLR p hθ

/-- Paper-language alias: the Bayes admit set is an actual-overlap threshold. -/
theorem fnch_overlap_admit_threshold (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ < θ₁) (prior : Prior) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ x : p.support,
      bayesAdmit (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior x ↔
        x ∈ overlapAdmissionThresholdSet p cut :=
  overlapNull_bayesAdmit_isThreshold p hθ prior

/--
Paper-language alias: the actual-overlap threshold minimizes finite Bayes risk
among deterministic admission sets.
-/
theorem fnch_overlap_threshold_bayes_optimal (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ < θ₁) (prior : Prior) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      bayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior
          (overlapAdmissionThresholdSet p cut) ≤
        bayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior R :=
  overlapNull_threshold_isBayesOptimal p hθ prior

/--
Paper-language alias: the actual-overlap threshold minimizes finite
cost-sensitive Bayes risk among deterministic admission sets.
-/
theorem fnch_overlap_costed_threshold_bayes_optimal (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      costedBayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior costs
          (overlapAdmissionThresholdSet p cut) ≤
        costedBayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior costs R :=
  overlapNull_costed_threshold_isBayesOptimal p hθ prior costs

end OrdvecFormalization
