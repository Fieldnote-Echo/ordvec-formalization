/-
# OrdvecFormalization.OverlapNull

The OrdVec / RankQuant candidate-generator *mechanism* (paper §6): the bitmap
popcount-overlap statistic `X = |Q_top ∩ D_top|` and the optimality of the
threshold admission rule `admit ⇔ X > t`.

Seeded from `takens-formalization` (Lean 4 `v4.28.0`, Mathlib `v4.28.0`), which
machine-checks the order-only monotone-invariance at the core of the ordinal
thesis. This file targets the *downstream* optimality result.

## Empirical grounding (done — gates this formalization)
The monotone-likelihood-ratio (MLR) precondition was validated on **real arXiv
embeddings** in the `ordvec` repo, branch `experiment/st-f-correlated-cb`:
under a shared-latent-support alternative the overlap `X` stochastically
dominates the **empirical** null and the likelihood ratio is monotone
non-decreasing in `X` (0/34 violations; LR 0.003 → 317.5).

## Scope discipline (keep two things distinct)
* The **theorems** below are about the admission RULE given a one-parameter
  overlap family with MLR — an abstract null `H₀` (`θ = 0`).
* The **deployment null is not the textbook hypergeometric.** On real embeddings
  the null overlap is *mean-shifted* (≈105 vs the hypergeometric 64) far more
  than it is variance-inflated. That is a corpus-CALIBRATION concern, *not* part
  of the optimality theorem. Do not conflate them.

## Status: SCAFFOLD
All proofs are `sorry`, but the statements are **non-vacuous** — they assert real
inequalities over explicit test regions (`power`, `aboveThreshold`, `bayesRisk`),
not `True`. Not yet built (`lake update && lake build` pending a Mathlib fetch);
treat the statements as best-effort drafts to refine against the API. Recommended
primary route is Bayes-optimality (reuse Mathlib `bayesRisk` / `posterior`),
cheaper than the full frequentist UMP tower — see the README spin-off-PR plan.
-/
import Mathlib

namespace OrdvecFormalization

/-- Overlap support: `X = |Q_top ∩ D_top| ∈ {0, …, nTop}`. -/
abbrev Overlap (nTop : ℕ) : Type := Fin (nTop + 1)

/-- A one-parameter family of pmfs on the overlap support, indexed by a real
    parameter `θ` (the log-odds / noncentrality of the **Fisher noncentral
    hypergeometric** alternative; `θ = 0` is the central hypergeometric null). -/
structure OverlapFamily (nTop : ℕ) where
  pmf : ℝ → Overlap nTop → ℝ
  nonneg : ∀ θ x, 0 ≤ pmf θ x
  sums_to_one : ∀ θ, Finset.univ.sum (fun x => pmf θ x) = 1

/-- **Monotone likelihood ratio in the overlap count.** For `θ₁ < θ₂` the ratio
    `pmf θ₂ x / pmf θ₁ x` is monotone non-decreasing in `x`. The Karlin–Rubin
    precondition — empirically validated on real embeddings (file header). -/
def HasMLR (nTop : ℕ) (F : OverlapFamily nTop) : Prop :=
  ∀ θ₁ θ₂, θ₁ < θ₂ →
    Monotone (fun x : Overlap nTop => F.pmf θ₂ x / F.pmf θ₁ x)

/-- Power of a rejection (admission) region `R` at parameter `θ`: `P_θ(X ∈ R)`. -/
def power (nTop : ℕ) (F : OverlapFamily nTop) (R : Finset (Overlap nTop)) (θ : ℝ) : ℝ :=
  R.sum (fun x => F.pmf θ x)

/-- The one-sided upper-tail region `{x | t < x}` — the threshold admission rule. -/
def aboveThreshold (nTop : ℕ) (t : Overlap nTop) : Finset (Overlap nTop) :=
  Finset.univ.filter (fun x => t < x)

/-- Bayes risk of region `R` under prior weight `π` on the alternative `θ₁`
    (vs null `θ₀`) with 0–1 loss: `π·P_θ₁(reject Hᵣ) + (1-π)·P_θ₀(accept Hᵣ)`,
    i.e. `π·(1 − power θ₁) + (1 − π)·power θ₀`. -/
def bayesRisk (nTop : ℕ) (F : OverlapFamily nTop) (θ₀ θ₁ π : ℝ)
    (R : Finset (Overlap nTop)) : ℝ :=
  π * (1 - power nTop F R θ₁) + (1 - π) * power nTop F R θ₀

/-- Unnormalised Fisher noncentral hypergeometric weight:
    `C(k, x) · C(nDim - k, nTop - x) · exp(θ · x)`. -/
noncomputable def fnchWeight (nDim k nTop : ℕ) (θ : ℝ) (x : Overlap nTop) : ℝ :=
  (k.choose x.val : ℝ) * ((nDim - k).choose (nTop - x.val) : ℝ)
    * Real.exp (θ * (x.val : ℝ))

/-- The Fisher noncentral hypergeometric overlap family (`θ = 0` ⇒ central
    hypergeometric null). Concretely defined; the `nonneg` / `sums_to_one`
    proof obligations are left as `sorry` (weights are `≥ 0`; the normaliser is
    `> 0` on the feasible support). -/
noncomputable def fnchFamily (nDim k nTop : ℕ) : OverlapFamily nTop where
  pmf := fun θ x =>
    fnchWeight nDim k nTop θ x / Finset.univ.sum (fun y => fnchWeight nDim k nTop θ y)
  nonneg := sorry
  sums_to_one := sorry

/-- **TARGET 1 (combinatorial core).** The Fisher noncentral hypergeometric
    overlap family has MLR in `X`: the pmf ratio in `θ` is `exp((θ₂−θ₁)·x)` up to
    an `x`-independent constant, hence monotone in `x`. (Mathlib gap N5.) -/
theorem fnchFamily_hasMLR (nDim k nTop : ℕ) :
    HasMLR nTop (fnchFamily nDim k nTop) :=
  sorry

/-- **TARGET 2 (frequentist UMP / Karlin–Rubin).** Given MLR, the threshold rule
    `aboveThreshold t` is uniformly most powerful at its level for
    `H₀ : θ = θ₀` vs `H₁ : θ > θ₀`: any region `R'` of no greater size at `θ₀`
    has no greater power at every `θ > θ₀`. (Deterministic-test form; the exact
    randomised-size version needs N6, the Neyman–Pearson lemma.) -/
theorem thresholdTest_isUMP
    (nTop : ℕ) (F : OverlapFamily nTop) (_hMLR : HasMLR nTop F)
    (θ₀ α : ℝ) (t : Overlap nTop)
    (_hlevel : power nTop F (aboveThreshold nTop t) θ₀ ≤ α) :
    ∀ R' : Finset (Overlap nTop), power nTop F R' θ₀ ≤ α →
      ∀ θ, θ₀ < θ →
        power nTop F R' θ ≤ power nTop F (aboveThreshold nTop t) θ :=
  sorry

/-- **TARGET 3 (recommended primary route — Bayes).** Given MLR, some threshold
    rule minimises the Bayes risk among all admission regions: the posterior
    odds are monotone in `X`, so the Bayes decision boundary is a single
    threshold. Reuse Mathlib `bayesRisk` / `posterior` / `boolKernel`. -/
theorem thresholdTest_isBayesOptimal
    (nTop : ℕ) (F : OverlapFamily nTop) (_hMLR : HasMLR nTop F)
    (θ₀ θ₁ π : ℝ) (_hθ : θ₀ < θ₁) (_hπ : 0 ≤ π ∧ π ≤ 1) :
    ∃ t : Overlap nTop, ∀ R' : Finset (Overlap nTop),
      bayesRisk nTop F θ₀ θ₁ π (aboveThreshold nTop t)
        ≤ bayesRisk nTop F θ₀ θ₁ π R' :=
  sorry

end OrdvecFormalization
