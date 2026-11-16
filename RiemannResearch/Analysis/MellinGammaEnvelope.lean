/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.DampedGammaStripBounds
import RiemannResearch.Analysis.VerticalResidueShift
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr

/-!
# Integrable polynomial Gamma envelopes

The quadratic weight is sufficient for both reflected zeta-square
Mellin contours. Continuity handles the real-axis point and the proved
arbitrary-order vertical Gamma estimate handles both tails.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set
namespace RiemannResearch.Analysis

theorem continuous_Gamma_vertical_of_neg_one_lt {a : ℝ}
    (ha : -1 < a) (ha0 : a ≠ 0) :
    Continuous (fun v : ℝ => Gamma ((a : ℂ) + v * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  have hΓ : DifferentiableAt ℂ Gamma ((a : ℂ) + v * I) := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have he := congrArg Complex.re hn
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul, sub_self, add_zero, neg_re, natCast_re] at he
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · exact ha0 (by simpa using he)
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      linarith
  exact hΓ.continuousAt.comp (f := fun v : ℝ => (a : ℂ) + v * I) (by fun_prop)

/-- A single integrable envelope for the two full vertical contour moments. -/
theorem integrable_Gamma_vertical_quadratic_weight {a : ℝ}
    (ha : -1 < a) (ha0 : a ≠ 0) :
    Integrable (fun v : ℝ => ‖Gamma ((a : ℂ) + v * I)‖ * (1+|v|)^2) := by
  have hcont : Continuous (fun v : ℝ =>
      Gamma ((a : ℂ) + v * I) * (((1+|v|)^2 : ℝ) : ℂ)) :=
    (continuous_Gamma_vertical_of_neg_one_lt ha ha0).mul (by fun_prop)
  obtain ⟨C, hC, hbound⟩ := Complex.exists_gamma_mul_cpow_neg_strip_pow_bound
    (lam := 1) (by norm_num) (a := a) (b := a) 4 (by norm_num; linarith)
  have hi : Integrable (fun v : ℝ =>
      Gamma ((a : ℂ) + v * I) * (((1+|v|)^2 : ℝ) : ℂ)) := by
    apply MeasureTheory.integrable_of_continuous_of_cauchy_tail hcont
      (B := 8*C) (T₀ := 1)
    intro v hv
    have hv0 : v ≠ 0 := by intro he; norm_num [he] at hv
    have hb : ‖Gamma ((a : ℂ) + v * I)‖ * |v|^4 ≤ C := by
      simpa using hbound a ⟨le_rfl, le_rfl⟩ v hv0
    have hsq : (1+|v|)^2 ≤ 4*|v|^2 := by nlinarith [abs_nonneg v]
    have hvsq : 1+v^2 ≤ 2*|v|^2 := by
      rw [sq_abs]
      have hh : (1 : ℝ) ≤ v^2 := by
        simpa only [one_pow, sq_abs] using
          pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hv 2
      linarith
    have hpoly : (1+|v|)^2 * (1+v^2) ≤ 8*|v|^4 := by
      calc
        _ ≤ (4*|v|^2) * (2*|v|^2) :=
          mul_le_mul hsq hvsq (by positivity) (by positivity)
        _ = _ := by ring
    have hmain :
        (‖Gamma ((a : ℂ) + v * I)‖ * (1+|v|)^2) * (1+v^2) ≤ 8*C := by
      calc
        _ = ‖Gamma ((a : ℂ) + v * I)‖ * ((1+|v|)^2 * (1+v^2)) := by ring
        _ ≤ ‖Gamma ((a : ℂ) + v * I)‖ * (8*|v|^4) :=
          mul_le_mul_of_nonneg_left hpoly (norm_nonneg _)
        _ = 8*(‖Gamma ((a : ℂ) + v * I)‖ * |v|^4) := by ring
        _ ≤ 8*C := mul_le_mul_of_nonneg_left hb (by norm_num)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _), ← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity : 0 < 1+v^2)).mpr hmain
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_sq] using hi.norm

end RiemannResearch.Analysis
