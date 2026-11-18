/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.UnitIntervalMassTail
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Fourier multipliers for dyadic width averages

The fixed-width triangle test in `MontgomeryWindowFourierVariance` is
`R^2 sinc(π R α)^2`. Its width average consists of an inverse-square term
independent of the endpoints and a signed endpoint term. Subtracting the
average on the half-sized interval cancels the inverse-square term exactly.
-/

noncomputable section

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/-- Mean of the Fourier triangle test over a width interval. -/
def widthMeanTriangleKernel (a b α : ℝ) : ℝ :=
  (∫ r in a..b, r ^ 2 * Real.sinc (Real.pi * r * α) ^ 2) / (b - a)

/-- At the central frequency, the multiplier is the mean squared width. -/
theorem widthMeanTriangleKernel_zero {a b : ℝ} (hab : a < b) :
    widthMeanTriangleKernel a b 0 = (a ^ 2 + a * b + b ^ 2) / 3 := by
  simp only [widthMeanTriangleKernel, mul_zero, Real.sinc_zero, one_pow, mul_one,
    integral_pow]
  field_simp [sub_ne_zero.mpr hab.ne']
  <;> ring

/-- The dyadic width contrast retains its explicit central contribution. -/
theorem dyadicWidthMeanTriangleKernel_zero {a b : ℝ} (hab : a < b) :
    widthMeanTriangleKernel a b 0 - widthMeanTriangleKernel (a / 2) (b / 2) 0 =
      (a ^ 2 + a * b + b ^ 2) / 4 := by
  rw [widthMeanTriangleKernel_zero hab, widthMeanTriangleKernel_zero (by linarith)]
  ring

/-- Exact signed endpoint correction to the universal inverse-square term. -/
theorem widthMeanTriangleKernel_eq {a b α : ℝ} (hab : a < b) (hα : α ≠ 0) :
    widthMeanTriangleKernel a b α =
      1 / (2 * (Real.pi * α) ^ 2) +
      (Real.sin (2 * (Real.pi * α) * a) - Real.sin (2 * (Real.pi * α) * b)) /
        (4 * (b - a) * (Real.pi * α) ^ 3) := by
  let k := Real.pi * α
  have hk : k ≠ 0 := mul_ne_zero Real.pi_ne_zero hα
  have hfun (r : ℝ) :
      r ^ 2 * Real.sinc (Real.pi * r * α) ^ 2 = Real.sin (r * k) ^ 2 / k ^ 2 := by
    rw [show Real.pi * r * α = r * k by dsimp [k]; ring]
    by_cases hr : r = 0
    · simp [hr]
    · rw [Real.sinc_of_ne_zero (mul_ne_zero hr hk)]
      field_simp [hr, hk]
      <;> ring
  have hscale := intervalIntegral.mul_integral_comp_mul_right (a := a) (b := b)
    (f := fun x : ℝ => Real.sin x ^ 2) k
  change k * (∫ r in a..b, Real.sin (r * k) ^ 2) =
    ∫ r in a * k..b * k, Real.sin r ^ 2 at hscale
  rw [integral_sin_sq] at hscale
  have hint : (∫ r in a..b, Real.sin (r * k) ^ 2) =
      ((Real.sin (a * k) * Real.cos (a * k) - Real.sin (b * k) * Real.cos (b * k) +
          b * k - a * k) / 2) / k := by
    apply (eq_div_iff hk).2
    rw [mul_comm]
    exact hscale
  unfold widthMeanTriangleKernel
  simp_rw [hfun]
  rw [intervalIntegral.integral_div, hint]
  change _ = 1 / (2 * k ^ 2) + (Real.sin (2 * k * a) - Real.sin (2 * k * b)) /
    (4 * (b - a) * k ^ 3)
  rw [show 2 * k * a = 2 * (a * k) by ring, show 2 * k * b = 2 * (b * k) by ring,
    Real.sin_two_mul, Real.sin_two_mul]
  field_simp [hk, sub_ne_zero.mpr hab.ne']
  <;> ring

/-- Exact difference of the two normalized width tests at nonzero frequency. -/
theorem dyadicWidthMeanTriangleKernel_eq {a b α : ℝ} (hab : a < b) (hα : α ≠ 0) :
    widthMeanTriangleKernel a b α - widthMeanTriangleKernel (a / 2) (b / 2) α =
      (Real.sin (2 * (Real.pi * α) * a) - Real.sin (2 * (Real.pi * α) * b) -
        2 * (Real.sin ((Real.pi * α) * a) - Real.sin ((Real.pi * α) * b))) /
        (4 * (b - a) * (Real.pi * α) ^ 3) := by
  have hhalf : a / 2 < b / 2 := by linarith
  rw [widthMeanTriangleKernel_eq hab hα, widthMeanTriangleKernel_eq hhalf hα,
    show 2 * (Real.pi * α) * (a / 2) = (Real.pi * α) * a by ring,
    show 2 * (Real.pi * α) * (b / 2) = (Real.pi * α) * b by ring,
    show b / 2 - a / 2 = (b - a) / 2 by ring]
  field_simp [Real.pi_ne_zero, hα, sub_ne_zero.mpr hab.ne']
  <;> ring

/-- The dyadic contrast gains one inverse power of frequency. -/
theorem abs_dyadicWidthMeanTriangleKernel_le {a b α : ℝ} (hab : a < b) (hα : α ≠ 0) :
    |widthMeanTriangleKernel a b α - widthMeanTriangleKernel (a / 2) (b / 2) α| ≤
      6 / (4 * (b - a) * (Real.pi * |α|) ^ 3) := by
  rw [dyadicWidthMeanTriangleKernel_eq hab hα, abs_div, abs_mul, abs_pow,
    abs_of_pos (mul_pos (by norm_num) (sub_pos.mpr hab)), abs_mul, abs_of_pos Real.pi_pos]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply abs_le.mpr
  constructor <;> linarith only [
    Real.neg_one_le_sin (2 * (Real.pi * α) * a), Real.sin_le_one (2 * (Real.pi * α) * a),
    Real.neg_one_le_sin (2 * (Real.pi * α) * b), Real.sin_le_one (2 * (Real.pi * α) * b),
    Real.neg_one_le_sin ((Real.pi * α) * a), Real.sin_le_one ((Real.pi * α) * a),
    Real.neg_one_le_sin ((Real.pi * α) * b), Real.sin_le_one ((Real.pi * α) * b)]

/-- The dyadic test sees a specific frequency strictly above unit support. -/
theorem dyadicWidthMeanTriangleKernel_three_halves :
    widthMeanTriangleKernel 1 2 (3 / 2) - widthMeanTriangleKernel (1 / 2) 1 (3 / 2) =
      4 / (27 * Real.pi ^ 3) := by
  have hs : Real.sin (Real.pi + Real.pi / 2) = -1 := by
    rw [Real.sin_add, Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two]
    ring
  have hpi (n : ℕ) : Real.sin ((n : ℝ) * Real.pi) = 0 := Real.sin_nat_mul_pi n
  have h := dyadicWidthMeanTriangleKernel_eq (a := 1) (b := 2) (α := 3 / 2)
    (by norm_num) (by norm_num)
  rw [show (2 : ℝ) / 2 = 1 by norm_num] at h
  rw [h, show 2 * (Real.pi * (3 / 2)) * 1 = (3 : ℕ) * Real.pi by norm_num <;> ring,
    show 2 * (Real.pi * (3 / 2)) * 2 = (6 : ℕ) * Real.pi by norm_num <;> ring,
    show Real.pi * (3 / 2) * 1 = Real.pi + Real.pi / 2 by ring,
    show Real.pi * (3 / 2) * 2 = (3 : ℕ) * Real.pi by norm_num <;> ring,
    hpi 3, hpi 6, hs]
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- An inverse-square tail for the actual dyadic sinc-square test. The
density's unit-interval mass bound is the only quantitative spectral input. -/
theorem integral_abs_dyadicWidthMeanTriangleKernel_mul_le
    {a b N B : ℝ} (hab : a < b) (hN : 1 < N) (hB : 0 ≤ B)
    {F : ℝ → ℝ} (hF : Continuous F) (hFnonneg : ∀ x, N ≤ x → 0 ≤ F x)
    (hmass : ∀ k : ℕ, (∫ x in N + k..N + k + 1, F x) ≤ B) (m : ℕ) :
    (∫ x in N..N + m,
      |(widthMeanTriangleKernel a b x - widthMeanTriangleKernel (a / 2) (b / 2) x) * F x|) ≤
      (6 / (4 * (b - a) * Real.pi ^ 3)) * B *
        (1 / (N - 1) ^ 2 - 1 / (N + m - 1) ^ 2) := by
  let W := fun x : ℝ => widthMeanTriangleKernel a b (max N x) -
    widthMeanTriangleKernel (a / 2) (b / 2) (max N x)
  have hpos (x : ℝ) : 0 < max N x := (by linarith : 0 < N).trans_le (le_max_left _ _)
  have hw : Continuous W := by
    change Continuous (fun x : ℝ => widthMeanTriangleKernel a b (max N x) -
      widthMeanTriangleKernel (a / 2) (b / 2) (max N x))
    rw [funext (fun x => dyadicWidthMeanTriangleKernel_eq hab (ne_of_gt (hpos x)))]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      have hx := hpos x
      have hba := sub_pos.mpr hab
      positivity
  have hdecay (x : ℝ) (hx : N ≤ x) :
      |W x| ≤ (6 / (4 * (b - a) * Real.pi ^ 3)) / x ^ 3 := by
    have hx0 : 0 < x := (by linarith : 0 < N).trans_le hx
    dsimp [W]
    rw [max_eq_right hx]
    have h := abs_dyadicWidthMeanTriangleKernel_le hab hx0.ne'
    rw [abs_of_pos hx0] at h
    apply h.trans_eq
    field_simp [hx0.ne', Real.pi_ne_zero, sub_ne_zero.mpr hab.ne']
    <;> ring
  have hba := sub_pos.mpr hab
  have ht := integral_abs_mul_le_of_unit_mass_inverse_cube hF hw hN hB
    (div_nonneg (by norm_num) (by positivity : 0 ≤ 4 * (b - a) * Real.pi ^ 3))
    hFnonneg hdecay hmass m
  apply Eq.trans_le _ ht
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg m))] at hx
  simp [W, max_eq_right hx.1]

end RiemannResearch.Analysis.MontgomeryPositiveGap
