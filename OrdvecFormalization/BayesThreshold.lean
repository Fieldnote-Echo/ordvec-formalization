/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import OrdvecFormalization.MLR

open scoped NNReal

namespace OrdvecFormalization

/-!
# Bayes threshold theorem

The finite Bayes risk is a pointwise sum. Under MLR, the pointwise Bayes admit
predicate is monotone, hence a threshold, and that threshold minimizes the risk.
-/

/-- Finite Bayes risk for an arbitrary deterministic admit set. -/
noncomputable def bayesRisk {n : ℕ} (p0 p1 : PosPMF n) (prior : Prior)
    (R : Set (Support n)) : ℝ≥0 :=
  by
    classical
    exact Finset.univ.sum fun x : Support n =>
      if x ∈ R then prior.compl * p0.mass x else prior.prob * p1.mass x

/-- Under MLR, the Bayes admit set is represented by a threshold. -/
theorem bayesAdmit_isThreshold {n : ℕ} (p0 p1 : PosPMF n) (prior : Prior)
    (hmlr : HasMLR p0 p1) :
    ∃ cut : Fin (n + 2), ∀ x : Support n,
      bayesAdmit p0 p1 prior x ↔ x ∈ thresholdSet n cut :=
  exists_threshold_of_monotone_pred n (bayesAdmit p0 p1 prior)
    (mlr_monotone_bayesAdmit p0 p1 prior hmlr)

/-- The threshold Bayes admit rule minimizes finite Bayes risk. -/
theorem threshold_bayesRisk_optimal {n : ℕ} (p0 p1 : PosPMF n) (prior : Prior)
    (hmlr : HasMLR p0 p1) :
    ∃ cut : Fin (n + 2), ∀ R : Set (Support n),
      bayesRisk p0 p1 prior (thresholdSet n cut) ≤ bayesRisk p0 p1 prior R := by
  rcases bayesAdmit_isThreshold p0 p1 prior hmlr with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro R
  dsimp [bayesRisk]
  refine Finset.sum_le_sum ?_
  intro x _hx
  by_cases hT : x ∈ thresholdSet n cut
  · have hA : bayesAdmit p0 p1 prior x := (hcut x).mpr hT
    by_cases hR : x ∈ R
    · simp [hT, hR]
    · simpa [hT, hR, bayesAdmit] using hA
  · have hA : ¬ bayesAdmit p0 p1 prior x := fun hx => hT ((hcut x).mp hx)
    by_cases hR : x ∈ R
    · have hReject : prior.prob * p1.mass x ≤ prior.compl * p0.mass x :=
        le_of_lt (lt_of_not_ge hA)
      simpa [hT, hR, bayesAdmit] using hReject
    · simp [hT, hR]

end OrdvecFormalization
