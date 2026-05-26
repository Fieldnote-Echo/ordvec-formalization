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

end OrdvecFormalization
