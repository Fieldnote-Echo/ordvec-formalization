/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import Lean.Elab.Tactic.Omega
import OrdvecFormalization.OverlapBayesOptimal
import OrdvecFormalization.BitmapNull

open scoped NNReal ENNReal

namespace OrdvecFormalization

/-!
# Constant-weight bitmap overlap thresholds

This file connects the canonical overlap-tilt theorem to the exact
constant-weight bitmap null.  The canonical signal theorem supplies a
Bayes-optimal actual-overlap cutoff; the bitmap null theorem identifies the
same numeric cutoff with a hypergeometric upper-tail probability under the
uniform `K`-active bitmap law.

Main definitions:
- `ConstantWeightBitmap`: the subtype of `K`-active bitmaps.
- `constantWeightBitmapOverlapEvidence`: literal bitmap overlap as feasible overlap
  evidence.
- `constantWeightBitmapUniformLaw`: the uniform finite law over `K`-active bitmap
  elements.

Main statements:
- `exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail`:
  arbitrary positive-base canonical signal model, with uniform-null tail
  calibration at the same cutoff.
- `exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail`:
  uniform-base, zero-null-tilt specialization where the model null is the
  uniform bitmap null.

-/

/-- FNCH overlap parameters for two `K`-active bitmaps in a `D`-coordinate universe. -/
def bitmapOverlapParams (D K : ℕ) (hK : K ≤ D) : FNCHParams where
  N := D
  k := K
  draws := K
  k_le_N := hK
  draws_le_N := hK

/-- Threshold cuts for the feasible overlap range of two `K`-active bitmaps. -/
abbrev BitmapCut (D K : ℕ) (hK : K ≤ D) :=
  Fin ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo + 2)

/-- The actual overlap threshold represented by a feasible bitmap cut. -/
def bitmapCutThreshold {D K : ℕ} (hK : K ≤ D) (cut : BitmapCut D K hK) : ℕ :=
  (bitmapOverlapParams D K hK).lo + cut.val

/-- The finite type of `K`-active bitmaps in a `D`-coordinate universe. -/
abbrev ConstantWeightBitmap (D K : ℕ) :=
  {d : Finset (BitmapCoord D) // d ∈ constantWeightBitmapSpace D K}

@[simp]
theorem constantWeightBitmap_card {D K : ℕ} (d : ConstantWeightBitmap D K) : d.val.card = K :=
  mem_constantWeightBitmapSpace_iff.mp d.property

/-- Uniform finite law over the `K`-active bitmap subtype. -/
noncomputable def constantWeightBitmapUniformLaw (D K : ℕ) (hK : K ≤ D) :
    FiniteLaw (ConstantWeightBitmap D K) where
  mass _ := ((D.choose K : ℝ≥0)⁻¹)
  pos _ := by
    have hchoose : 0 < (D.choose K : ℝ≥0) := by
      exact_mod_cast Nat.choose_pos hK
    exact inv_pos.mpr hchoose
  sum_one := by
    have hcard : Fintype.card (ConstantWeightBitmap D K) = D.choose K := by
      simp [ConstantWeightBitmap]
    have hchoose : (D.choose K : ℝ≥0) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hK
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    exact mul_inv_cancel₀ hchoose

/-- The literal overlap tail event on the `K`-active bitmap subtype. -/
def constantWeightBitmapOverlapTailSet (D K t : ℕ) (q : Finset (BitmapCoord D)) :
    Set (ConstantWeightBitmap D K) :=
  {d | t ≤ bitmapOverlap q d.val}

theorem bitmapOverlapParams_lo_le_overlap {D K : ℕ} (hK : K ≤ D)
    {q d : Finset (BitmapCoord D)} (hq : q.card = K) (hd : d.card = K) :
    (bitmapOverlapParams D K hK).lo ≤ bitmapOverlap q d := by
  have hUnionLe : (q ∪ d).card ≤ D := by
    simpa [Fintype.card_fin] using
      (Finset.card_le_univ (q ∪ d : Finset (BitmapCoord D)))
  have hCard : (q ∪ d).card + bitmapOverlap q d = K + K := by
    simpa [bitmapOverlap, hq, hd] using Finset.card_union_add_card_inter q d
  change K + K - D ≤ bitmapOverlap q d
  omega

theorem bitmapOverlap_le_bitmapOverlapParams_hi {D K : ℕ} (hK : K ≤ D)
    {q d : Finset (BitmapCoord D)} (hq : q.card = K) :
    bitmapOverlap q d ≤ (bitmapOverlapParams D K hK).hi := by
  have hOverlap : bitmapOverlap q d ≤ K := by
    rw [bitmapOverlap, ← hq]
    exact Finset.card_le_card Finset.inter_subset_left
  simpa [bitmapOverlapParams, FNCHParams.hi] using hOverlap

/--
Literal bitmap overlap, shifted into the feasible FNCH support for two
`K`-active bitmaps.
-/
def constantWeightBitmapOverlapEvidence {D K : ℕ} (hK : K ≤ D)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    ConstantWeightBitmap D K → (bitmapOverlapParams D K hK).support :=
  fun d =>
    let p : FNCHParams := bitmapOverlapParams D K hK
    let x := bitmapOverlap q d.val - p.lo
    ⟨x, by
      have hd : d.val.card = K := constantWeightBitmap_card d
      have hlo : p.lo ≤ bitmapOverlap q d.val :=
        bitmapOverlapParams_lo_le_overlap hK hq hd
      have hhi : bitmapOverlap q d.val ≤ p.hi :=
        bitmapOverlap_le_bitmapOverlapParams_hi hK hq
      change bitmapOverlap q d.val - p.lo < p.hi - p.lo + 1
      omega⟩

@[simp]
theorem constantWeightBitmapOverlapEvidence_overlap {D K : ℕ} (hK : K ≤ D)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) (d : ConstantWeightBitmap D K) :
    (bitmapOverlapParams D K hK).overlap (constantWeightBitmapOverlapEvidence hK hq d) =
      bitmapOverlap q d.val := by
  let p : FNCHParams := bitmapOverlapParams D K hK
  have hd : d.val.card = K := constantWeightBitmap_card d
  have hlo : p.lo ≤ bitmapOverlap q d.val :=
    bitmapOverlapParams_lo_le_overlap hK hq hd
  simp [constantWeightBitmapOverlapEvidence, FNCHParams.overlap, p, Nat.add_sub_of_le hlo]

/-- Pulled-back actual-overlap quotient thresholds are literal bitmap overlap tails. -/
theorem overlapQuotientThresholdSet_constantWeightBitmapOverlapEvidence_eq {D K : ℕ}
    (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    (cut : Fin ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo + 2)) :
    overlapQuotientThresholdSet (bitmapOverlapParams D K hK)
        (fun d : ConstantWeightBitmap D K => d) (constantWeightBitmapOverlapEvidence hK hq) cut =
      constantWeightBitmapOverlapTailSet D K ((bitmapOverlapParams D K hK).lo + cut.val) q := by
  ext d
  simp [overlapQuotientThresholdSet, actualOverlapThresholdSet, constantWeightBitmapOverlapTailSet]

/--
Finite Bayes-risk theorem with exact bitmap-null calibration.

For a canonical overlap tilt on the feasible overlap support of two `K`-active
bitmaps, the produced Bayes-optimal threshold has a hypergeometric upper-tail
probability under the uniform bitmap null at the same actual-overlap cutoff.
-/
theorem exists_overlapQuotientThreshold_finiteBayesRisk_le_and_bitmapHypergeomTail
    {Ω Ωq : Type} [Fintype Ω] {D K : ℕ} (hK : K ≤ D)
    (base : FiniteLaw Ω) (Q : Ω → Ωq)
    (O : Ωq → (bitmapOverlapParams D K hK).support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (hprior : 0 < prior.prob)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    ∃ cut : Fin ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo + 2),
      (∀ R : Set Ω,
        finiteBayesRisk
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
            prior (overlapQuotientThresholdSet (bitmapOverlapParams D K hK) Q O cut) ≤
          finiteBayesRisk
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
            prior R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapOverlapParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapOverlapParams D K hK).lo + cut.val) : ℝ≥0∞) := by
  let p : FNCHParams := bitmapOverlapParams D K hK
  rcases exists_overlapQuotientThreshold_finiteBayesRisk_le_of_canonicalTilt_of_lt
      p base Q O hθ prior hprior with ⟨cut, hopt⟩
  refine ⟨cut, hopt, ?_⟩
  simpa [p] using
    (bitmapUniformPMF_overlapTail_prob (D := D) (K := K)
      (t := p.lo + cut.val) hK (q := q) hq)

/--
Constant-weight bitmap specialization of the finite Bayes-risk theorem.

Here the full observation space is the finite type of `K`-active bitmaps, and
the evidence statistic is literal bitmap overlap. The Bayes-optimal canonical
tilt rule is exactly the bitmap overlap tail event whose null probability is the
hypergeometric upper tail.
-/
theorem exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    (base : FiniteLaw (ConstantWeightBitmap D K))
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (hprior : 0 < prior.prob) :
    ∃ cut : Fin ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo + 2),
      (∀ R : Set (ConstantWeightBitmap D K),
        finiteBayesRisk
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₁)
            prior
            (constantWeightBitmapOverlapTailSet D K ((bitmapOverlapParams D K hK).lo + cut.val) q) ≤
          finiteBayesRisk
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₁)
            prior R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapOverlapParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapOverlapParams D K hK).lo + cut.val) : ℝ≥0∞) := by
  let p : FNCHParams := bitmapOverlapParams D K hK
  let O := constantWeightBitmapOverlapEvidence hK hq
  rcases exists_overlapQuotientThreshold_finiteBayesRisk_le_of_canonicalTilt_of_lt
      p base (fun d : ConstantWeightBitmap D K => d) O hθ prior hprior with
    ⟨cut, hopt⟩
  refine ⟨cut, ?_, ?_⟩
  · intro R
    have hevent :
        overlapQuotientThresholdSet p (fun d : ConstantWeightBitmap D K => d) O cut =
          constantWeightBitmapOverlapTailSet D K (p.lo + cut.val) q := by
      simpa [p, O] using
        (overlapQuotientThresholdSet_constantWeightBitmapOverlapEvidence_eq hK hq cut)
    simpa [p, O, hevent] using hopt R
  · simpa [p] using
      (bitmapUniformPMF_overlapTail_prob (D := D) (K := K)
        (t := p.lo + cut.val) hK (q := q) hq)

/--
Cost-sensitive theorem with exact bitmap-null calibration.

The asymmetric-cost version has the same form: priors and costs select a
Bayes-optimal cutoff, and the bitmap null gives the exact hypergeometric tail
mass at that cutoff.
-/
theorem exists_overlapQuotientThreshold_finiteCostedBayesRisk_le_and_bitmapHypergeomTail
    {Ω Ωq : Type} [Fintype Ω] {D K : ℕ} (hK : K ≤ D)
    (base : FiniteLaw Ω) (Q : Ω → Ωq)
    (O : Ωq → (bitmapOverlapParams D K hK).support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    ∃ cut : Fin ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo + 2),
      (∀ R : Set Ω,
        finiteCostedBayesRisk
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
            prior costs
            (overlapQuotientThresholdSet (bitmapOverlapParams D K hK) Q O cut) ≤
          finiteCostedBayesRisk
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
            prior costs R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapOverlapParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapOverlapParams D K hK).lo + cut.val) : ℝ≥0∞) := by
  let p : FNCHParams := bitmapOverlapParams D K hK
  rcases exists_overlapQuotientThreshold_finiteCostedBayesRisk_le_of_canonicalTilt_of_lt
      p base Q O hθ prior costs hw1 with ⟨cut, hopt⟩
  refine ⟨cut, hopt, ?_⟩
  simpa [p] using
    (bitmapUniformPMF_overlapTail_prob (D := D) (K := K)
      (t := p.lo + cut.val) hK (q := q) hq)

/-- Cost-sensitive constant-weight bitmap specialization. -/
theorem exists_constantWeightBitmapOverlapTail_finiteCostedBayesRisk_le_and_hypergeomTail
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    (base : FiniteLaw (ConstantWeightBitmap D K))
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob) :
    ∃ cut : Fin ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo + 2),
      (∀ R : Set (ConstantWeightBitmap D K),
        finiteCostedBayesRisk
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₁)
            prior costs
            (constantWeightBitmapOverlapTailSet D K ((bitmapOverlapParams D K hK).lo + cut.val) q) ≤
          finiteCostedBayesRisk
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₁)
            prior costs R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapOverlapParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapOverlapParams D K hK).lo + cut.val) : ℝ≥0∞) := by
  let p : FNCHParams := bitmapOverlapParams D K hK
  let O := constantWeightBitmapOverlapEvidence hK hq
  rcases exists_overlapQuotientThreshold_finiteCostedBayesRisk_le_of_canonicalTilt_of_lt
      p base (fun d : ConstantWeightBitmap D K => d) O hθ prior costs hw1 with ⟨cut, hopt⟩
  refine ⟨cut, ?_, ?_⟩
  · intro R
    have hevent :
        overlapQuotientThresholdSet p (fun d : ConstantWeightBitmap D K => d) O cut =
          constantWeightBitmapOverlapTailSet D K (p.lo + cut.val) q := by
      simpa [p, O] using
        (overlapQuotientThresholdSet_constantWeightBitmapOverlapEvidence_eq hK hq cut)
    simpa [p, O, hevent] using hopt R
  · simpa [p] using
      (bitmapUniformPMF_overlapTail_prob (D := D) (K := K)
        (t := p.lo + cut.val) hK (q := q) hq)

/--
Uniform-null specialization of the bitmap theorem.

Here the base law is uniform over `K`-active bitmaps and the null signal
parameter is `0`, so the negative-class model is the zero-tilt of the uniform
bitmap law.
-/
theorem exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    {θ : ℝ} (hθ : 0 < θ) (prior : Prior) (hprior : 0 < prior.prob) :
    ∃ cut : BitmapCut D K hK,
      (∀ R : Set (ConstantWeightBitmap D K),
        finiteBayesRisk
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) θ)
            prior
            (constantWeightBitmapOverlapTailSet D K (bitmapCutThreshold hK cut) q) ≤
          finiteBayesRisk
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) θ)
            prior R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K (bitmapCutThreshold hK cut) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K (bitmapCutThreshold hK cut) : ℝ≥0∞) := by
  simpa [BitmapCut, bitmapCutThreshold, bitmapOverlapParams] using
    (exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
      hK hq (constantWeightBitmapUniformLaw D K hK)
      hθ prior hprior)

/-- Cost-sensitive uniform-null specialization of the bitmap theorem. -/
theorem exists_uniformBitmapOverlapTail_finiteCostedBayesRisk_le_and_hypergeomTail
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    {θ : ℝ} (hθ : 0 < θ) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob) :
    ∃ cut : BitmapCut D K hK,
      (∀ R : Set (ConstantWeightBitmap D K),
        finiteCostedBayesRisk
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) θ)
            prior costs
            (constantWeightBitmapOverlapTailSet D K (bitmapCutThreshold hK cut) q) ≤
          finiteCostedBayesRisk
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) θ)
            prior costs R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K (bitmapCutThreshold hK cut) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K (bitmapCutThreshold hK cut) : ℝ≥0∞) := by
  simpa [BitmapCut, bitmapCutThreshold, bitmapOverlapParams] using
    (exists_constantWeightBitmapOverlapTail_finiteCostedBayesRisk_le_and_hypergeomTail
      hK hq (constantWeightBitmapUniformLaw D K hK)
      hθ prior costs hw1)

end OrdvecFormalization
