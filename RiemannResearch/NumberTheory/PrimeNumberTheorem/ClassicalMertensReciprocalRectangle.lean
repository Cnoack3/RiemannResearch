/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.ClassicalReciprocalMertens
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# Low heights in the classical Mertens contour

Lee and Leong, arXiv:2208.06141v5, Section 5.1 use bounds at large and small
heights when shifting the integral for the Möbius sum. For a qualitative
constant, compactness after removal of the pole supplies the small-height
estimate here. The reciprocal evaluated by Lean at the single point
`s = 1` is included separately in the bound.
-/

noncomputable section
open Complex Filter Set
open scoped Topology
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem
open Quantitative.ClassicalRegion

/-- On a compact zero-free set the raw reciprocal is bounded, including its
value at one. Its removable extension has limit zero there. -/
private theorem bounded_inverse_zeta_on_compact {S : Set ℂ} (hS : IsCompact S)
    (hzero : ∀ s ∈ S, riemannZeta s ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ S, ‖(riemannZeta s)⁻¹‖ ≤ B := by
  let f : ℂ → ℂ := fun s => if s = 1 then 0 else (riemannZeta s)⁻¹
  have hcont : ContinuousOn f S := by
    intro s hs
    by_cases h : s = 1
    · subst s
      apply ContinuousAt.continuousWithinAt
      rw [continuousAt_iff_punctured_nhds]
      change Tendsto f (𝓝[≠] (1 : ℂ)) (𝓝 (if (1:ℂ) = 1 then 0 else (riemannZeta 1)⁻¹))
      rw [if_pos rfl]
      have hn : Tendsto (fun z : ℂ => z - (1 : ℂ)) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
        have ht := (continuous_id.tendsto (1 : ℂ)).sub (tendsto_const_nhds (x := (1 : ℂ)))
        simpa using ht.mono_left (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ))
      have ht := hn.div riemannZeta_residue_one one_ne_zero
      rw [zero_div] at ht
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin,
        riemannZeta_residue_one.eventually (compl_singleton_mem_nhds one_ne_zero)] with z hz hprod
      rw [show f z = (riemannZeta z)⁻¹ from if_neg (show z ≠ 1 from hz)]
      change (z - 1) / ((z - 1) * riemannZeta z) = (riemannZeta z)⁻¹
      field_simp [sub_ne_zero.mpr (show z ≠ 1 from hz), right_ne_zero_of_mul hprod]
    · have hf : f =ᶠ[𝓝 s] fun z => (riemannZeta z)⁻¹ := by
        filter_upwards [compl_singleton_mem_nhds h] with z hz
        exact if_neg (show z ≠ 1 from hz)
      have hz := ((analyticAt_riemannZeta h).inv (hzero s hs)).continuousAt
      exact (hz.congr_of_eventuallyEq hf).continuousWithinAt
  obtain ⟨K, hK⟩ := hS.bddAbove_image hcont.norm
  refine ⟨max K ‖(riemannZeta 1)⁻¹‖, (norm_nonneg _).trans (le_max_right _ _), ?_⟩
  intro s hs
  rcases eq_or_ne s 1 with rfl | hn
  · exact le_max_right _ _
  · have h := hK (Set.mem_image_of_mem (fun z => ‖f z‖) hs)
    exact (by simpa [f, hn] using h : ‖(riemannZeta s)⁻¹‖ ≤ K).trans (le_max_left _ _)

/-- The same width gives logarithmic-square bounds on all contour segments
and a zero-free closed rectangle. Above the truncation height the bound is
only needed to the right of the line one. -/
theorem classical_mertens_reciprocal_rectangle :
    ∃ a ∈ Ioo (0:ℝ) (1/42), a ≤ F ∧
      (∃ C > (0:ℝ), ∀ {X T : ℝ}, 3 < X → 3 < T →
        ∀ {σ t : ℝ}, (1 ≤ σ ∨ |t| ≤ T) →
          σ ∈ Icc (1-a/Real.log T) (1+(Real.log X)⁻¹) →
          1 / ‖riemannZeta ((σ:ℂ) + t * I)‖ ≤ C * (Real.log (2 + |t|))^2) ∧
      (∀ T : ℝ, 3 ≤ T → ∀ s ∈ (Icc (1-a/Real.log T) 2 ×ℂ Icc (-T) T),
        riemannZeta s ≠ 0) := by
  obtain ⟨a, ha, haF, K, hK, hhigh⟩ := classical_inv_zeta_high_strip
  obtain ⟨b, hb, hbzero⟩ := ZetaZeroFree1
  obtain ⟨u, hu, hulow⟩ := ZetaNoZerosInBox 4
  let A := min (min a b) (1-u)
  have hA : 0 < A := lt_min (lt_min ha hb.1) (by linarith)
  have hAa : A ≤ a := (min_le_left _ _).trans (min_le_left _ _)
  have hAb : A ≤ b := (min_le_left _ _).trans (min_le_right _ _)
  have hAu : A ≤ 1-u := min_le_right _ _
  let S : Set ℂ := Icc u 2 ×ℂ Icc (-4) 4
  have hSc : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  have hzero (s : ℂ) (hs : s ∈ S) : riemannZeta s ≠ 0 := by
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hs
    rw [← Complex.re_add_im s]
    exact hulow s.im (abs_le.mpr him) s.re hre.1
  obtain ⟨B, hB, hbnd⟩ := bounded_inverse_zeta_on_compact hSc hzero
  have hfloor {T : ℝ} (hT : 3 ≤ T) : u ≤ 1-A/Real.log T := by
    have h1 := div_le_self hA.le (logt_gt_one hT).le
    linarith
  have hwidth {t T v : ℝ} (ht : 4 ≤ |t|) (htT : |t| ≤ T) (hAv : A ≤ v) :
      A / Real.log T ≤ v / Real.log |t| := by
    have hl : 0 < Real.log |t| := Real.log_pos (by linarith)
    have hmon : Real.log |t| ≤ Real.log T := Real.log_le_log (by linarith) htT
    exact (div_le_div_of_nonneg_left hA.le hl hmon).trans (div_le_div_of_nonneg_right hAv hl.le)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C := max K (B/(Real.log 2)^2)
  have hC : 0 < C := hK.trans_le (le_max_left _ _)
  refine ⟨A, ⟨hA, (hAa.trans haF).trans_lt FinIoo.2⟩, hAa.trans haF, ⟨C, hC, ?_⟩, ?_⟩
  · intro X T hX hT σ t hpos hσ
    have hσ2 : σ ≤ 2 := hσ.2.trans (Quantitative.one_add_inv_log hX.le).le
    rw [one_div, ← norm_inv]
    by_cases ht : 4 ≤ |t|
    · have hσa : 1-a/Real.log |t| ≤ σ := by
        rcases hpos with h | h
        · exact (sub_le_self _ (div_nonneg ha.le (Real.log_nonneg (by linarith)))).trans h
        · exact (sub_le_sub_left (hwidth ht h hAa) 1).trans hσ.1
      exact (hhigh σ t ht hσa hσ2).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    · have hsre : u ≤ σ := (hfloor hT.le).trans hσ.1
      have hs : ((σ:ℂ) + t * I) ∈ S := Complex.mem_reProdIm.mpr (by
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          zero_mul, sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
        exact ⟨⟨hsre,hσ2⟩, abs_le.mp (lt_of_not_ge ht).le⟩)
      have hscale : B ≤ C * (Real.log 2)^2 :=
        (div_le_iff₀ (sq_pos_of_pos hlog2)).mp (le_max_right _ _)
      have hlog : Real.log 2 ≤ Real.log (2+|t|) :=
        Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
      exact (hbnd _ hs).trans (hscale.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlog2.le hlog 2) hC.le))
  · intro T hT s hs
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hs
    have hTt : |s.im| ≤ T := abs_le.mpr him
    by_cases ht : 4 ≤ |s.im|
    · rcases le_or_gt 1 s.re with hr | hr
      · exact riemannZeta_ne_zero_of_one_le_re hr
      · rw [← Complex.re_add_im s]
        apply hbzero s.re s.im (by linarith)
        rw [Real.rpow_one]
        exact ⟨(sub_le_sub_left (hwidth ht hTt hAb) 1).trans hre.1, hr⟩
    · exact hzero s (Complex.mem_reProdIm.mpr
        ⟨⟨(hfloor hT).trans hre.1, hre.2⟩, abs_le.mp (lt_of_not_ge ht).le⟩)

end RiemannResearch.NumberTheory.PrimeNumberTheorem
