/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import OrdvecFormalization.Headline
import OrdvecFormalization.BitmapNull

open scoped NNReal ENNReal

namespace OrdvecFormalization

/-!
# Bitmap-calibrated headline theorem

This file connects the paper-facing canonical overlap-tilt theorem to the exact
constant-composition bitmap null.  The canonical signal theorem supplies a
Bayes-optimal actual-overlap cutoff; the bitmap null theorem calibrates the
same numeric cutoff as a hypergeometric upper-tail probability under the
uniform `K`-active bitmap law.

Main definitions:
- `BitmapDoc`: the subtype of `K`-active document bitmaps.
- `bitmapDocOverlapEvidence`: literal bitmap overlap as feasible overlap
  evidence.
- `bitmapDocUniformLaw`: the uniform finite law over `K`-active bitmap
  documents.

Main statements:
- `ordvec_bitmap_headline_theorem`: arbitrary positive-base canonical signal
  model, with uniform-null tail calibration at the same cutoff.
- `ordvec_bitmap_uniform_null_headline_theorem`: uniform-base, zero-null-tilt
  specialization where the model null is the uniform bitmap null.

Implementation note:
`bitmapFNCHParams` is retained for compatibility with the existing feasible
overlap support API.  The public-facing alias is `bitmapOverlapParams`.
-/

/-- FNCH overlap parameters for two `K`-active bitmaps in a `D`-coordinate universe. -/
def bitmapFNCHParams (D K : ℕ) (hK : K ≤ D) : FNCHParams where
  N := D
  k := K
  draws := K
  k_le_N := hK
  draws_le_N := hK

/-- Feasible overlap parameters for two `K`-active bitmaps in a `D`-coordinate universe. -/
abbrev bitmapOverlapParams (D K : ℕ) (hK : K ≤ D) : FNCHParams :=
  bitmapFNCHParams D K hK

/-- Threshold cuts for the feasible overlap range of two `K`-active bitmaps. -/
abbrev BitmapCut (D K : ℕ) (hK : K ≤ D) :=
  Fin ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo + 2)

/-- The actual overlap threshold represented by a feasible bitmap cut. -/
def bitmapCutThreshold {D K : ℕ} (hK : K ≤ D) (cut : BitmapCut D K hK) : ℕ :=
  (bitmapOverlapParams D K hK).lo + cut.val

/-- The finite type of `K`-active bitmap documents. -/
abbrev BitmapDoc (D K : ℕ) := {d : Finset (BitmapCoord D) // d ∈ bitmapSpace D K}

@[simp]
theorem bitmapDoc_card {D K : ℕ} (d : BitmapDoc D K) : d.val.card = K :=
  mem_bitmapSpace_iff.mp d.property

/-- Uniform finite law over the `K`-active bitmap document subtype. -/
noncomputable def bitmapDocUniformLaw (D K : ℕ) (hK : K ≤ D) :
    FiniteLaw (BitmapDoc D K) where
  mass _ := ((D.choose K : ℝ≥0)⁻¹)
  pos _ := by
    have hchoose : 0 < (D.choose K : ℝ≥0) := by
      exact_mod_cast Nat.choose_pos hK
    exact inv_pos.mpr hchoose
  sum_one := by
    have hcard : Fintype.card (BitmapDoc D K) = D.choose K := by
      simp [BitmapDoc]
    have hchoose : (D.choose K : ℝ≥0) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hK
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    exact mul_inv_cancel₀ hchoose

/-- The literal overlap tail event on the `K`-active bitmap document subtype. -/
def bitmapDocOverlapTailSet (D K t : ℕ) (q : Finset (BitmapCoord D)) :
    Set (BitmapDoc D K) :=
  {d | t ≤ bitmapOverlap q d.val}

theorem bitmapFNCHParams_lo_le_overlap {D K : ℕ} (hK : K ≤ D)
    {q d : Finset (BitmapCoord D)} (hq : q.card = K) (hd : d.card = K) :
    (bitmapFNCHParams D K hK).lo ≤ bitmapOverlap q d := by
  have hUnionLe : (q ∪ d).card ≤ D := by
    simpa [Fintype.card_fin] using
      (Finset.card_le_univ (q ∪ d : Finset (BitmapCoord D)))
  have hCard : (q ∪ d).card + bitmapOverlap q d = K + K := by
    simpa [bitmapOverlap, hq, hd] using Finset.card_union_add_card_inter q d
  change K + K - D ≤ bitmapOverlap q d
  omega

theorem bitmapOverlap_le_bitmapFNCHParams_hi {D K : ℕ} (hK : K ≤ D)
    {q d : Finset (BitmapCoord D)} (hq : q.card = K) :
    bitmapOverlap q d ≤ (bitmapFNCHParams D K hK).hi := by
  have hOverlap : bitmapOverlap q d ≤ K := by
    rw [bitmapOverlap, ← hq]
    exact Finset.card_le_card Finset.inter_subset_left
  simpa [bitmapFNCHParams, FNCHParams.hi] using hOverlap

/--
Literal bitmap overlap, shifted into the feasible FNCH support for two
`K`-active bitmaps.
-/
def bitmapDocOverlapEvidence {D K : ℕ} (hK : K ≤ D)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    BitmapDoc D K → (bitmapFNCHParams D K hK).support :=
  fun d =>
    let p : FNCHParams := bitmapFNCHParams D K hK
    let x := bitmapOverlap q d.val - p.lo
    ⟨x, by
      have hd : d.val.card = K := bitmapDoc_card d
      have hlo : p.lo ≤ bitmapOverlap q d.val :=
        bitmapFNCHParams_lo_le_overlap hK hq hd
      have hhi : bitmapOverlap q d.val ≤ p.hi :=
        bitmapOverlap_le_bitmapFNCHParams_hi hK hq
      change bitmapOverlap q d.val - p.lo < p.hi - p.lo + 1
      omega⟩

@[simp]
theorem bitmapDocOverlapEvidence_overlap {D K : ℕ} (hK : K ≤ D)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) (d : BitmapDoc D K) :
    (bitmapFNCHParams D K hK).overlap (bitmapDocOverlapEvidence hK hq d) =
      bitmapOverlap q d.val := by
  let p : FNCHParams := bitmapFNCHParams D K hK
  have hd : d.val.card = K := bitmapDoc_card d
  have hlo : p.lo ≤ bitmapOverlap q d.val :=
    bitmapFNCHParams_lo_le_overlap hK hq hd
  simp [bitmapDocOverlapEvidence, FNCHParams.overlap, p, Nat.add_sub_of_le hlo]

/--
On concrete bitmap documents, pulled-back actual-overlap quotient thresholds
are exactly the literal bitmap overlap tail event.
-/
theorem overlapQuotientThresholdSet_bitmapDocOverlapEvidence_eq {D K : ℕ}
    (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    (cut : Fin ((bitmapFNCHParams D K hK).hi - (bitmapFNCHParams D K hK).lo + 2)) :
    overlapQuotientThresholdSet (bitmapFNCHParams D K hK)
        (fun d : BitmapDoc D K => d) (bitmapDocOverlapEvidence hK hq) cut =
      bitmapDocOverlapTailSet D K ((bitmapFNCHParams D K hK).lo + cut.val) q := by
  ext d
  simp [overlapQuotientThresholdSet, actualOverlapThresholdSet, bitmapDocOverlapTailSet]

/--
Bayes-prior headline theorem with exact bitmap-null calibration.

For canonical overlap-tilted relevance evidence on the feasible overlap support
of two `K`-active bitmaps, the produced Bayes-optimal threshold has a
hypergeometric upper-tail false-positive probability under the uniform bitmap
null at the same actual-overlap cutoff.
-/
theorem ordvec_headline_theorem_with_bitmap_null
    {Ω Ωq : Type} [Fintype Ω] {D K : ℕ} (hK : K ≤ D)
    (base : FiniteLaw Ω) (Q : Ω → Ωq)
    (O : Ωq → (bitmapFNCHParams D K hK).support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (hprior : 0 < prior.prob)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    ∃ cut : Fin ((bitmapFNCHParams D K hK).hi - (bitmapFNCHParams D K hK).lo + 2),
      (∀ R : Set Ω,
        finiteBayesRisk
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
            prior (overlapQuotientThresholdSet (bitmapFNCHParams D K hK) Q O cut) ≤
          finiteBayesRisk
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
            prior R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapFNCHParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapFNCHParams D K hK).lo + cut.val) : ℝ≥0∞) := by
  let p : FNCHParams := bitmapFNCHParams D K hK
  rcases ordvec_headline_theorem p base Q O hθ prior hprior with ⟨cut, hopt⟩
  refine ⟨cut, hopt, ?_⟩
  simpa [p] using
    (bitmapUniformPMF_overlapTail_prob (D := D) (K := K)
      (t := p.lo + cut.val) hK (q := q) hq)

/--
Concrete bitmap-document version of the headline theorem.

Here the full observation space is the finite type of `K`-active bitmap
documents, and the evidence statistic is literal bitmap overlap with the query.
The Bayes-optimal canonical signal rule is exactly the bitmap overlap tail event
whose null probability is the hypergeometric upper tail.
-/
theorem bitmap_doc_tail_bayes_optimal_with_null
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    (base : FiniteLaw (BitmapDoc D K))
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (hprior : 0 < prior.prob) :
    ∃ cut : Fin ((bitmapFNCHParams D K hK).hi - (bitmapFNCHParams D K hK).lo + 2),
      (∀ R : Set (BitmapDoc D K),
        finiteBayesRisk
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₁)
            prior
            (bitmapDocOverlapTailSet D K ((bitmapFNCHParams D K hK).lo + cut.val) q) ≤
          finiteBayesRisk
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₁)
            prior R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapFNCHParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapFNCHParams D K hK).lo + cut.val) : ℝ≥0∞) := by
  let p : FNCHParams := bitmapFNCHParams D K hK
  let O := bitmapDocOverlapEvidence hK hq
  rcases ordvec_headline_theorem p base (fun d : BitmapDoc D K => d) O hθ prior hprior with
    ⟨cut, hopt⟩
  refine ⟨cut, ?_, ?_⟩
  · intro R
    have hevent :
        overlapQuotientThresholdSet p (fun d : BitmapDoc D K => d) O cut =
          bitmapDocOverlapTailSet D K (p.lo + cut.val) q := by
      simpa [p, O] using
        (overlapQuotientThresholdSet_bitmapDocOverlapEvidence_eq hK hq cut)
    simpa [p, O, hevent] using hopt R
  · simpa [p] using
      (bitmapUniformPMF_overlapTail_prob (D := D) (K := K)
        (t := p.lo + cut.val) hK (q := q) hq)

/--
Cost-sensitive headline theorem with exact bitmap-null calibration.

The asymmetric-cost version has the same form: priors and costs select a
Bayes-optimal cutoff, and the bitmap null gives the exact hypergeometric
false-positive tail at that cutoff.
-/
theorem ordvec_headline_costed_theorem_with_bitmap_null
    {Ω Ωq : Type} [Fintype Ω] {D K : ℕ} (hK : K ≤ D)
    (base : FiniteLaw Ω) (Q : Ω → Ωq)
    (O : Ωq → (bitmapFNCHParams D K hK).support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    ∃ cut : Fin ((bitmapFNCHParams D K hK).hi - (bitmapFNCHParams D K hK).lo + 2),
      (∀ R : Set Ω,
        finiteCostedBayesRisk
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
            prior costs
            (overlapQuotientThresholdSet (bitmapFNCHParams D K hK) Q O cut) ≤
          finiteCostedBayesRisk
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
            prior costs R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapFNCHParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapFNCHParams D K hK).lo + cut.val) : ℝ≥0∞) := by
  let p : FNCHParams := bitmapFNCHParams D K hK
  rcases ordinal_retrieval_sufficient_for_canonical_overlap_tilt_costed_of_lt
      p base Q O hθ prior costs hw1 with ⟨cut, hopt⟩
  refine ⟨cut, hopt, ?_⟩
  simpa [p] using
    (bitmapUniformPMF_overlapTail_prob (D := D) (K := K)
      (t := p.lo + cut.val) hK (q := q) hq)

/-- Cost-sensitive concrete bitmap-document version of the calibrated headline theorem. -/
theorem bitmap_doc_tail_costed_bayes_optimal_with_null
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    (base : FiniteLaw (BitmapDoc D K))
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob) :
    ∃ cut : Fin ((bitmapFNCHParams D K hK).hi - (bitmapFNCHParams D K hK).lo + 2),
      (∀ R : Set (BitmapDoc D K),
        finiteCostedBayesRisk
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₁)
            prior costs
            (bitmapDocOverlapTailSet D K ((bitmapFNCHParams D K hK).lo + cut.val) q) ≤
          finiteCostedBayesRisk
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₁)
            prior costs R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapFNCHParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapFNCHParams D K hK).lo + cut.val) : ℝ≥0∞) := by
  let p : FNCHParams := bitmapFNCHParams D K hK
  let O := bitmapDocOverlapEvidence hK hq
  rcases ordinal_retrieval_sufficient_for_canonical_overlap_tilt_costed_of_lt
      p base (fun d : BitmapDoc D K => d) O hθ prior costs hw1 with ⟨cut, hopt⟩
  refine ⟨cut, ?_, ?_⟩
  · intro R
    have hevent :
        overlapQuotientThresholdSet p (fun d : BitmapDoc D K => d) O cut =
          bitmapDocOverlapTailSet D K (p.lo + cut.val) q := by
      simpa [p, O] using
        (overlapQuotientThresholdSet_bitmapDocOverlapEvidence_eq hK hq cut)
    simpa [p, O, hevent] using hopt R
  · simpa [p] using
      (bitmapUniformPMF_overlapTail_prob (D := D) (K := K)
        (t := p.lo + cut.val) hK (q := q) hq)

/--
Paper-facing bitmap headline theorem.

Under the canonical finite overlap-tilt signal model on `K`-active bitmap
documents, literal overlap-tail retrieval is Bayes-optimal among all
deterministic bitmap-document admission rules; under the uniform
constant-composition bitmap null, the same event has exactly the
hypergeometric upper-tail probability.
-/
theorem ordvec_bitmap_headline_theorem
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    (base : FiniteLaw (BitmapDoc D K))
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (hprior : 0 < prior.prob) :
    ∃ cut : Fin ((bitmapFNCHParams D K hK).hi - (bitmapFNCHParams D K hK).lo + 2),
      (∀ R : Set (BitmapDoc D K),
        finiteBayesRisk
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₁)
            prior
            (bitmapDocOverlapTailSet D K ((bitmapFNCHParams D K hK).lo + cut.val) q) ≤
          finiteBayesRisk
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₁)
            prior R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapFNCHParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapFNCHParams D K hK).lo + cut.val) : ℝ≥0∞) :=
  bitmap_doc_tail_bayes_optimal_with_null hK hq base hθ prior hprior

/-- Cost-sensitive paper-facing bitmap headline theorem. -/
theorem ordvec_bitmap_costed_headline_theorem
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    (base : FiniteLaw (BitmapDoc D K))
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob) :
    ∃ cut : Fin ((bitmapFNCHParams D K hK).hi - (bitmapFNCHParams D K hK).lo + 2),
      (∀ R : Set (BitmapDoc D K),
        finiteCostedBayesRisk
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₁)
            prior costs
            (bitmapDocOverlapTailSet D K ((bitmapFNCHParams D K hK).lo + cut.val) q) ≤
          finiteCostedBayesRisk
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (bitmapDocOverlapEvidence hK hq) θ₁)
            prior costs R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapFNCHParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapFNCHParams D K hK).lo + cut.val) : ℝ≥0∞) :=
  bitmap_doc_tail_costed_bayes_optimal_with_null hK hq base hθ prior costs hw1

/--
Uniform-null specialization of the bitmap headline theorem.

Here the base law is uniform over `K`-active bitmap documents and the null signal
parameter is `0`, so the negative-class model is the zero-tilt of the uniform
bitmap law.
-/
theorem ordvec_bitmap_uniform_null_headline_theorem
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    {θ : ℝ} (hθ : 0 < θ) (prior : Prior) (hprior : 0 < prior.prob) :
    ∃ cut : BitmapCut D K hK,
      (∀ R : Set (BitmapDoc D K),
        finiteBayesRisk
            (finiteExponentialTilt (bitmapDocUniformLaw D K hK)
              (bitmapDocOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (bitmapDocUniformLaw D K hK)
              (bitmapDocOverlapEvidence hK hq) θ)
            prior
            (bitmapDocOverlapTailSet D K (bitmapCutThreshold hK cut) q) ≤
          finiteBayesRisk
            (finiteExponentialTilt (bitmapDocUniformLaw D K hK)
              (bitmapDocOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (bitmapDocUniformLaw D K hK)
              (bitmapDocOverlapEvidence hK hq) θ)
            prior R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K (bitmapCutThreshold hK cut) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K (bitmapCutThreshold hK cut) : ℝ≥0∞) := by
  simpa [BitmapCut, bitmapCutThreshold, bitmapOverlapParams] using
    (ordvec_bitmap_headline_theorem hK hq (bitmapDocUniformLaw D K hK)
      hθ prior hprior)

/-- Cost-sensitive uniform-null specialization of the bitmap headline theorem. -/
theorem ordvec_bitmap_uniform_null_costed_headline_theorem
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    {θ : ℝ} (hθ : 0 < θ) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob) :
    ∃ cut : BitmapCut D K hK,
      (∀ R : Set (BitmapDoc D K),
        finiteCostedBayesRisk
            (finiteExponentialTilt (bitmapDocUniformLaw D K hK)
              (bitmapDocOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (bitmapDocUniformLaw D K hK)
              (bitmapDocOverlapEvidence hK hq) θ)
            prior costs
            (bitmapDocOverlapTailSet D K (bitmapCutThreshold hK cut) q) ≤
          finiteCostedBayesRisk
            (finiteExponentialTilt (bitmapDocUniformLaw D K hK)
              (bitmapDocOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (bitmapDocUniformLaw D K hK)
              (bitmapDocOverlapEvidence hK hq) θ)
            prior costs R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K (bitmapCutThreshold hK cut) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K (bitmapCutThreshold hK cut) : ℝ≥0∞) := by
  simpa [BitmapCut, bitmapCutThreshold, bitmapOverlapParams] using
    (ordvec_bitmap_costed_headline_theorem hK hq (bitmapDocUniformLaw D K hK)
      hθ prior costs hw1)

end OrdvecFormalization
