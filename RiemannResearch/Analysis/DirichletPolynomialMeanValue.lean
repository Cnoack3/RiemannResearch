/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ComplexGaussianMeanValue
import RiemannResearch.Analysis.GaussianCellGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform second moments of finite Dirichlet polynomials

Source for the target: Chourasiya--Simonic, *An explicit form of Ingham's
zero density estimate*, https://arxiv.org/html/2507.15184v2, Sections 4 and 5.1.
This elementary Gaussian-majorant proof supplies an upper mean value for
arbitrary complex coefficients; no sharp asymptotic remainder is asserted.

Logarithmic separation makes the complete Gaussian matrix bounded by the
existing integer-cell envelope. Translation preserves coefficient norms,
so the final bound uses the actual length of an arbitrary real interval.
The RH-program consumer is the actual Mobius mollifier's I2 obligation.
-/
noncomputable section
open MeasureTheory Complex Set
open scoped BigOperators


namespace Real
theorem sub_le_mul_log_sub_of_le {x y X : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyX : y ≤ X) :
    y - x ≤ X * (Real.log y - Real.log x) := by
  have hy : 0 < y := hx.trans_le hxy
  have hl := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at hl
  have hm := mul_le_mul_of_nonneg_right hl hy.le
  have he : (x / y - 1) * y = x - y := by field_simp
  rw [he] at hm
  have hlog : 0 ≤ Real.log y - Real.log x := sub_nonneg.mpr (Real.log_le_log hx hxy)
  have hb := mul_le_mul_of_nonneg_right hyX hlog
  nlinarith

theorem abs_sub_le_mul_abs_log_sub_of_le {x y X : ℝ}
    (hx : 0 < x) (hxX : x ≤ X) (hy : 0 < y) (hyX : y ≤ X) :
    |x - y| ≤ X * |Real.log x - Real.log y| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hx hxy))]
    simpa only [neg_sub] using sub_le_mul_log_sub_of_le hx hxy hyX
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy hyx))]
    exact sub_le_mul_log_sub_of_le hy hyx hxX
end Real

namespace RiemannResearch.Analysis
open GaussianCellGeometry
theorem gaussian_log_row_le {X : ℕ} {L : ℝ} (hL : 2 * (X : ℝ) ≤ L)
    {m : ℕ} (hm : m ∈ Finset.Icc 1 X) :
    (∑ n ∈ Finset.Icc 1 X, Real.exp (-L ^ 2 * (Real.log m - Real.log n) ^ 2 / 2)) ≤ 6 := by
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 X) :
      Real.exp (-L ^ 2 * (Real.log m - Real.log n) ^ 2 / 2) ≤ cellKernel (m : ℤ) (n : ℤ) := by
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hmx : (m : ℝ) ≤ X := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hnx : (n : ℝ) ≤ X := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hd := Real.abs_sub_le_mul_abs_log_sub_of_le hm0 hmx hn0 hnx
    have hg : |(m : ℝ) - n| ≤ (L / 2) * |Real.log m - Real.log n| :=
      hd.trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
    have hs := pow_le_pow_left₀ (abs_nonneg ((m : ℝ) - n)) hg 2
    rw [sq_abs, mul_pow, sq_abs, div_pow] at hs
    calc
      _ ≤ Real.exp (-((m : ℝ) - n) ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg ((m : ℝ) - n)]
      _ ≤ _ := by simpa using gaussian_le_cellKernel (m : ℝ) (n : ℝ)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, cellKernel (m : ℤ) (n : ℤ) := Finset.sum_le_sum hterm
    _ = ∑ z ∈ (Finset.Icc 1 X).image (fun n : ℕ => (n : ℤ)), cellKernel (m : ℤ) z := by
      rw [Finset.sum_image (by
        intro a ha b hb hab
        exact Int.ofNat_injective hab)]
    _ ≤ 6 := cellKernel_row_le _ _

/-- Uniform mean value for arbitrary complex Dirichlet coefficients. -/
theorem dirichlet_polynomial_second_moment_le (X : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hX : 0 < X) :
    (∫ t in (0 : ℝ)..T,
      ‖∑ n ∈ Finset.Icc 1 X, a n * Complex.exp (Complex.I * t * (-Real.log n))‖ ^ 2) ≤
      (12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) * (T + X) *
        ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2 := by
  have hXr : 0 < (X : ℝ) := by exact_mod_cast hX
  have hb := Complex.integral_exp_sum_le_of_gaussian_rows
    (Finset.Icc 1 X) a (fun n => -Real.log n)
    (T := T) (L := T + 2 * X) (D := 6) hT (by positivity) (by linarith)
    (by
      intro m hm
      have hr := gaussian_log_row_le (L := T + 2 * X) (by linarith) hm
      simpa only [neg_sub_neg, sub_sq_comm] using hr)
  simp only [Complex.ofReal_neg] at hb
  apply hb.trans
  have hsum : 0 ≤ ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : 0 ≤ Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ) := by positivity
  nlinarith [mul_nonneg hc hT, mul_nonneg (mul_nonneg hc hT) hsum]

/-- Translation-uniform mean value; the cost uses the actual interval length. -/
theorem dirichlet_polynomial_second_moment_window_le (X : ℕ) (a : ℕ → ℂ)
    {H T : ℝ} (hHT : H ≤ T) (hX : 0 < X) :
    (∫ t in H..T,
      ‖∑ n ∈ Finset.Icc 1 X, a n * Complex.exp (Complex.I * t * (-Real.log n))‖ ^ 2) ≤
      (12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) * (T - H + X) *
        ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2 := by
  let b : ℕ → ℂ := fun n => a n * Complex.exp (Complex.I * H * (-Real.log n))
  have hshift (t : ℝ) :
      (∑ n ∈ Finset.Icc 1 X, a n * Complex.exp (Complex.I * (t + H) * (-Real.log n))) =
        ∑ n ∈ Finset.Icc 1 X, b n * Complex.exp (Complex.I * t * (-Real.log n)) := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [b]
    conv_rhs => rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have he :
      (∫ t in H..T, ‖∑ n ∈ Finset.Icc 1 X, a n *
        Complex.exp (Complex.I * t * (-Real.log n))‖ ^ 2) =
      (∫ t in (0 : ℝ)..(T - H), ‖∑ n ∈ Finset.Icc 1 X, b n *
        Complex.exp (Complex.I * t * (-Real.log n))‖ ^ 2) := by
    have hi := intervalIntegral.integral_comp_add_right
      (a := (0 : ℝ)) (b := T - H)
      (fun t : ℝ => ‖∑ n ∈ Finset.Icc 1 X,
        a n * Complex.exp (Complex.I * t * (-Real.log n))‖ ^ 2) H
    simpa only [zero_add, sub_add_cancel, Complex.ofReal_add, hshift] using hi.symm
  have hn (n : ℕ) : ‖b n‖ = ‖a n‖ := by
    dsimp [b]
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      mul_zero, zero_mul, add_zero, zero_add, neg_zero, sub_zero, Real.exp_zero, mul_one]
  rw [he]
  simpa only [hn] using dirichlet_polynomial_second_moment_le X b (sub_nonneg.mpr hHT) hX

end RiemannResearch.Analysis
