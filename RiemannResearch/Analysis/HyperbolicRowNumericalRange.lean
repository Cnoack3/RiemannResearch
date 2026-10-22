/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Numerical upper range of a signed hyperbolic row

Source: balanced exponential channels in the user-requested hyperbolic
lower-bound analysis (2026-10-05). The sum/difference identity keeps the
negative channel, and rescaling gives the sharp rank-two upper coefficient.
ActualHyperbolicTailFrames specializes the result to the actual zero copies.
The closed power-sum spectrum is discussed separately in
RH/ActualHyperbolicLowerBounds20261005.md.
-/

noncomputable section
open scoped BigOperators InnerProductSpace

namespace RiemannResearch.Analysis.CenteredHyperbolicFrames
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem balancedRow_form_eq (u v f : E) :
    ‖(inner ℂ u f+inner ℂ v f)/(2:ℂ)‖^2-
      ‖(inner ℂ u f-inner ℂ v f)/(2:ℂ)‖^2 =
      (inner ℂ u f*star (inner ℂ v f)).re := by
  have htwo : ‖(2:ℂ)‖ = 2 := by norm_num
  simp only [norm_div, htwo, div_pow, Complex.sq_norm,
    Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring
theorem balancedRow_form_upper (u v f : E) :
    ‖(inner ℂ u f+inner ℂ v f)/(2:ℂ)‖^2-
      ‖(inner ℂ u f-inner ℂ v f)/(2:ℂ)‖^2 ≤
      (‖u+v‖^2/4)*‖f‖^2 := by
  have hCS := norm_inner_le_norm (𝕜 := ℂ) (u+v) f
  have hsq : ‖inner ℂ (u+v) f‖^2 ≤ (‖u+v‖*‖f‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hCS
  have htwo : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [inner_add_left] at hsq
  simp only [norm_div, htwo]
  nlinarith [sq_nonneg (‖inner ℂ u f-inner ℂ v f‖)]

theorem balancedRow_form_upper_of_balanced (u v f : E) (p d : ℝ)
    (hu : ‖u‖^2=p) (hv : ‖v‖^2=p) (huv : (inner ℂ u v).re=d) :
    ‖(inner ℂ u f+inner ℂ v f)/(2:ℂ)‖^2-
      ‖(inner ℂ u f-inner ℂ v f)/(2:ℂ)‖^2 ≤
      ((p+d)/2)*‖f‖^2 := by
  have hadd : ‖u+v‖^2 = 2*(p+d) := by
    calc
      _ = ‖u‖^2+2*(inner ℂ u v).re+‖v‖^2 := norm_add_sq (𝕜 := ℂ) u v
      _ = _ := by rw [hu, hv, huv]; ring
  have hh := balancedRow_form_upper u v f
  rw [hadd] at hh
  convert hh using 1 <;> ring

theorem rankTwoCross_form_upper (u v f : E) :
    (inner ℂ u f*star (inner ℂ v f)).re ≤
      ((‖u‖*‖v‖+(inner ℂ u v).re)/2)*‖f‖^2 := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  let p : ℝ := ‖u‖*‖v‖
  have hp : 0 < p := mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
  let U : E := (‖v‖:ℂ) • u
  let V : E := (‖u‖:ℂ) • v
  have hU : ‖U‖^2 = p^2 := by
    simp only [U, p, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg v)]
    ring
  have hV : ‖V‖^2 = p^2 := by
    simp only [V, p, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg u)]
  have hUV : (inner ℂ U V).re = p*(inner ℂ u v).re := by
    simp only [U, V, inner_smul_left, inner_smul_right, Complex.star_def,
      Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    dsimp [p]
    ring
  have hh := balancedRow_form_upper_of_balanced U V f (p^2)
    (p*(inner ℂ u v).re) hU hV hUV
  rw [balancedRow_form_eq] at hh
  have hcrossC : inner ℂ U f*star (inner ℂ V f) =
      (p : ℂ)*(inner ℂ u f*star (inner ℂ v f)) := by
    simp only [U, V, inner_smul_left, star_mul, star_star,
      Complex.star_def, Complex.conj_ofReal]
    dsimp [p]
    push_cast
    ring
  have hcross : (inner ℂ U f*star (inner ℂ V f)).re =
      p*(inner ℂ u f*star (inner ℂ v f)).re := by
    rw [hcrossC]
    simp
  rw [hcross] at hh
  change (inner ℂ u f*star (inner ℂ v f)).re ≤ ((p+(inner ℂ u v).re)/2)*‖f‖^2
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith

/-- The negative form has the complementary rank-two coefficient. -/
theorem rankTwoCross_form_neg_upper (u v f : E) :
    -(inner ℂ u f*star (inner ℂ v f)).re ≤
      ((‖u‖*‖v‖-(inner ℂ u v).re)/2)*‖f‖^2 := by
  have h := rankTwoCross_form_upper u (-v) f
  simpa only [inner_neg_left, inner_neg_right, star_neg, mul_neg,
    Complex.neg_re, norm_neg, sub_eq_add_neg] using h

end RiemannResearch.Analysis.CenteredHyperbolicFrames
