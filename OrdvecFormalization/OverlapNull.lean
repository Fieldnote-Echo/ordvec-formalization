/-
# OrdvecFormalization.OverlapNull

The OrdVec / RankQuant candidate-generator *mechanism* (paper §6): the bitmap
popcount-overlap statistic `X = |Q_top ∩ D_top|` and the optimality of the
threshold admission rule `admit ⇔ X > t★`.

Seeded from `takens-formalization` (Lean 4 `v4.28.0`, Mathlib `v4.28.0`), which
machine-checks the order-only monotone-invariance at the core of the ordinal
thesis. This file targets the *downstream* optimality result.

## Empirical grounding (done — gates this formalization)
The monotone-likelihood-ratio (MLR) precondition was validated on **real arXiv
embeddings** in the `ordvec` repo, branch `experiment/st-f-correlated-cb`:
under a shared-latent-support alternative the overlap `X` stochastically
dominates the **empirical** null and the likelihood ratio is monotone
non-decreasing in `X` (0/34 violations; LR 0.003 → 317.5). So the statements
below are worth proving, not merely plausible.

## Scope discipline (keep two things distinct)
* The **theorem** is about the admission RULE given a one-parameter overlap
  family with MLR — an abstract null `H₀` (`θ = 0`).
* The **deployment null is not the textbook hypergeometric.** On real embeddings
  the null overlap is *mean-shifted* (≈105 vs the hypergeometric 64) far more
  than it is variance-inflated (`experiment/st-e-null-calibration`,
  `experiment/st-f-correlated-cb`). That is a corpus-CALIBRATION concern, *not*
  part of the optimality theorem. Do not conflate them.

## Status: SCAFFOLD
All proofs are `sorry`. The statements are DRAFTS to be refined against the
Mathlib API and are **not yet built** (`lake update && lake build` pending a
Mathlib fetch). `import Mathlib` is the catch-all; narrow it once the proofs
settle. Recommended primary route is Bayes-optimality (reuse Mathlib
`bayesRisk` / `posterior`), cheaper than the full frequentist UMP tower — see
the README spin-off-PR plan (N1 hypergeometric PMF, N5 MLR, N6 Neyman–Pearson,
N7 Karlin–Rubin).
-/
import Mathlib

namespace OrdvecFormalization

open scoped BigOperators

/-- Overlap support: `X = |Q_top ∩ D_top| ∈ {0, …, nTop}`. -/
abbrev Overlap (nTop : ℕ) : Type := Fin (nTop + 1)

/-- A one-parameter family of pmfs on the overlap support, indexed by a real
    parameter `θ` (the log-odds / noncentrality of the **Fisher noncentral
    hypergeometric** alternative; `θ = 0` is the central hypergeometric null). -/
structure OverlapFamily (nTop : ℕ) where
  pmf : ℝ → Overlap nTop → ℝ
  nonneg : ∀ θ x, 0 ≤ pmf θ x
  sums_to_one : ∀ θ, ∑ x, pmf θ x = 1

/-- **Monotone likelihood ratio in the overlap count.** For `θ₁ < θ₂` the ratio
    `pmf θ₂ x / pmf θ₁ x` is monotone non-decreasing in `x`. This is the
    Karlin–Rubin precondition — empirically validated on real embeddings
    (see the file header). -/
def HasMLR (nTop : ℕ) (F : OverlapFamily nTop) : Prop :=
  ∀ θ₁ θ₂, θ₁ < θ₂ →
    Monotone (fun x : Overlap nTop => F.pmf θ₂ x / F.pmf θ₁ x)

/-- The Fisher noncentral hypergeometric overlap family.
    `pmf θ x ∝ C(k, x) · C(nDim - k, nTop - x) · exp (θ · x)`, normalised over
    the feasible support. `θ = 0` recovers the central hypergeometric null.
    TODO: construct (N1 — hypergeometric PMF is missing from Mathlib). -/
noncomputable def fnchFamily (nDim k nTop : ℕ) : OverlapFamily nTop :=
  sorry

/-- **TARGET 1 (combinatorial core).** The Fisher noncentral hypergeometric
    overlap family has MLR in `X`. The pmf ratio in `θ` is `exp((θ₂-θ₁)·x)` up
    to an `x`-independent constant, hence monotone in `x`. (N5) -/
theorem fnchFamily_hasMLR (nDim k nTop : ℕ) :
    HasMLR nTop (fnchFamily nDim k nTop) :=
  sorry

/-- **TARGET 2 (frequentist).** Given MLR, the one-sided threshold test
    “admit ⇔ `X > t`” is **uniformly most powerful** at its level for
    `H₀ : θ ≤ 0` vs `H₁ : θ > 0` (Karlin–Rubin). Depends on the Neyman–Pearson
    lemma (N6), the dominant missing-from-Mathlib piece. -/
theorem thresholdTest_isUMP
    (nTop : ℕ) (F : OverlapFamily nTop) (_hMLR : HasMLR nTop F)
    (t : Overlap nTop) (_θ₀ : ℝ) :
    -- `IsUMP (admitAbove t) level H₀ H₁` once the test/UMP scaffolding is in place.
    True :=
  sorry

/-- **TARGET 3 (recommended primary route — Bayes).** Under 0–1 loss and a prior
    `π` on {relevant, null}, the Bayes-optimal decision is a **threshold on `X`**.
    Reuse Mathlib `bayesRisk` / `posterior` / `boolKernel`; MLR ⇒ the posterior
    odds are monotone in `X` ⇒ the Bayes decision boundary is a single threshold.
    Cheaper than the UMP tower; this is the launch-target theorem. -/
theorem thresholdTest_isBayesOptimal
    (nTop : ℕ) (F : OverlapFamily nTop) (_hMLR : HasMLR nTop F)
    (_π : ℝ) :
    True :=
  sorry

end OrdvecFormalization
