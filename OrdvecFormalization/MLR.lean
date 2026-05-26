/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import OrdvecFormalization.FiniteDecision

open scoped NNReal

/-!
# Monotone likelihood ratio

This file states MLR in cross-multiplication form and proves that it makes the
Bayes admit predicate monotone.
-/

/-- Bayes admits `H₁` at `x` exactly when the pointwise `H₁` loss is no larger. -/
def bayesAdmit {n : ℕ} (p0 p1 : PosPMF n) (π : ℝ≥0) (x : Support n) : Prop :=
  (1 - π) * p0.mass x ≤ π * p1.mass x

/--
Cross-multiplication monotone likelihood ratio.

This avoids division in the theorem statement; strict positivity is used only
when canceling a common factor in the monotonicity proof.
-/
def HasMLR {n : ℕ} (p0 p1 : PosPMF n) : Prop :=
  ∀ x y : Support n, x ≤ y → p1.mass x * p0.mass y ≤ p1.mass y * p0.mass x

/-- MLR implies that the Bayes admit predicate is monotone on the support. -/
theorem mlr_monotone_bayesAdmit {n : ℕ} (p0 p1 : PosPMF n) (π : ℝ≥0)
    (hmlr : HasMLR p0 p1) :
    Monotone (bayesAdmit p0 p1 π) := by
  intro x y hxy hx
  dsimp [bayesAdmit] at hx ⊢
  have hleft :
      (1 - π) * p0.mass x * p0.mass y ≤ π * p1.mass x * p0.mass y := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_left hx (p0.mass y)
  have hright :
      π * p1.mass x * p0.mass y ≤ π * p1.mass y * p0.mass x := by
    simpa [mul_assoc] using mul_le_mul_right (hmlr x y hxy) π
  have hchain :
      (1 - π) * p0.mass y * p0.mass x ≤ π * p1.mass y * p0.mass x := by
    calc
      (1 - π) * p0.mass y * p0.mass x =
          (1 - π) * p0.mass x * p0.mass y := by
        ac_rfl
      _ ≤ π * p1.mass x * p0.mass y := hleft
      _ ≤ π * p1.mass y * p0.mass x := hright
  exact (mul_le_mul_iff_left₀ (p0.pos x)).mp hchain
