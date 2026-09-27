/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import RiemannResearch.Analysis.LogPowerSummability

/-!
# Quantitative logarithmic p-series tail at exponent three halves

The exact improper integral is evaluated by the primitive
`-2 * (6 + log x)^(-1/2)`. Mathlib's integral comparison then gives
the discrete tail, with one extra initial summand. This is elementary
analysis used by the quantitative half-damped arithmetic Hilbert limit.
Source: the integral test and fundamental theorem of calculus as formalized
in Mathlib.Analysis.SumIntegralComparisons and
Mathlib.MeasureTheory.Integral.IntegralEqImproper.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace RiemannResearch.Analysis

private theorem log_kernel_threeHalves_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ 1 / (x * (6 + Real.log x) ^ (3 / 2 : ℝ)) := by
  have hlog := Real.log_nonneg hx
  positivity

private theorem log_kernel_threeHalves_antitone {a : ℝ} (ha : 1 ≤ a) :
    AntitoneOn (fun x : ℝ => 1 / (x * (6 + Real.log x) ^ (3 / 2 : ℝ)))
      (Ici a) := by
  intro x hx y hy hxy
  have hx1 : 1 ≤ x := ha.trans hx
  have hy1 : 1 ≤ y := ha.trans hy
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hLx : 0 < 6 + Real.log x := by linarith [Real.log_nonneg hx1]
  have hLy : 0 < 6 + Real.log y := by linarith [Real.log_nonneg hy1]
  apply one_div_le_one_div_of_le
    (mul_pos hx0 (Real.rpow_pos_of_pos hLx _))
  exact mul_le_mul hxy
    (Real.rpow_le_rpow hLx.le (by linarith [Real.log_le_log hx0 hxy]) (by norm_num))
    (Real.rpow_nonneg hLx.le _) hy0.le

private theorem log_kernel_threeHalves_primitive {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (fun t : ℝ => -2 * (6 + Real.log t) ^ (-(1 / 2 : ℝ)))
      (1 / (x * (6 + Real.log x) ^ (3 / 2 : ℝ))) x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < 6 + Real.log x := by linarith [Real.log_nonneg hx]
  have h := (((Real.hasDerivAt_log hx0.ne').const_add 6).rpow_const
    (p := -(1 / 2 : ℝ)) (Or.inl hL.ne')).const_mul (-2)
  apply h.congr_deriv
  rw [show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by ring,
    Real.rpow_neg hL.le]
  simp only [one_div, mul_inv_rev]
  ring

private theorem log_kernel_threeHalves_primitive_tendsto :
    Tendsto (fun t : ℝ => -2 * (6 + Real.log t) ^ (-(1 / 2 : ℝ)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun t : ℝ => 6 + Real.log t) atTop atTop :=
    tendsto_atTop_mono (fun t => by linarith) Real.tendsto_log_atTop
  simpa only [Function.comp_def, mul_zero] using
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hlog).const_mul (-2)

theorem integrable_log_kernel_threeHalves {a : ℝ} (ha : 1 ≤ a) :
    IntegrableOn (fun x : ℝ => 1 / (x * (6 + Real.log x) ^ (3 / 2 : ℝ)))
      (Ioi a) := by
  exact integrableOn_Ioi_deriv_of_nonneg
    (log_kernel_threeHalves_primitive ha).continuousAt.continuousWithinAt
    (fun x hx => log_kernel_threeHalves_primitive (ha.trans hx.le))
    (fun x hx => log_kernel_threeHalves_nonneg (ha.trans hx.le))
    log_kernel_threeHalves_primitive_tendsto

/-- Exact logarithmic integral used in the endpoint rate. -/
theorem integral_log_kernel_threeHalves {a : ℝ} (ha : 1 ≤ a) :
    (∫ x : ℝ in Ioi a, 1 / (x * (6 + Real.log x) ^ (3 / 2 : ℝ))) =
      2 * (6 + Real.log a) ^ (-(1 / 2 : ℝ)) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (log_kernel_threeHalves_primitive ha).continuousAt.continuousWithinAt
    (fun x hx => log_kernel_threeHalves_primitive (ha.trans hx.le))
    (integrable_log_kernel_threeHalves ha) log_kernel_threeHalves_primitive_tendsto
  simpa only [zero_sub, neg_mul, neg_neg] using h

/-- The shifted logarithmic kernel is summable, including the harmless zero coordinate. -/
theorem summable_shifted_log_threeHalves :
    Summable (fun n : ℕ =>
      1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ (3 / 2 : ℝ))) := by
  have hs := summable_log_power_majorant (p := (3 / 2 : ℝ)) (by norm_num)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlpos : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by linarith)
  have hshift : Real.log (2 * (n : ℝ)) ≤ 6 + Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne']
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (log_kernel_threeHalves_nonneg hn1)]
  apply one_div_le_one_div_of_le
    (mul_pos hn0 (Real.rpow_pos_of_pos hlpos (3 / 2 : ℝ)))
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hlpos.le hshift (by norm_num : (0 : ℝ) ≤ 3 / 2)) hn0.le

/-- An explicit logarithmic tail estimate, including the initial term at `M`. -/
theorem log_power_tail_threeHalves {M : ℕ} (hM : 1 ≤ M) :
    (∑' k : ℕ, 1 / (((k + M : ℕ) : ℝ) *
      (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (3 / 2 : ℝ))) ≤
      3 * (6 + Real.log (M : ℝ)) ^ (-(1 / 2 : ℝ)) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hL : 0 < 6 + Real.log (M : ℝ) := by linarith [Real.log_nonneg hM1]
  have hi : (∑' k : ℕ, 1 / (((k + M + 1 : ℕ) : ℝ) *
      (6 + Real.log ((k + M + 1 : ℕ) : ℝ)) ^ (3 / 2 : ℝ))) ≤
      2 * (6 + Real.log (M : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ ∫ x : ℝ in Ioi (M : ℝ),
          1 / (x * (6 + Real.log x) ^ (3 / 2 : ℝ)) :=
        AntitoneOn.tsum_comp_add_le_integral M
          (log_kernel_threeHalves_antitone hM1)
          (integrable_log_kernel_threeHalves hM1)
          (fun x hx => log_kernel_threeHalves_nonneg (hM1.trans hx.le))
      _ = _ := integral_log_kernel_threeHalves hM1
  have hfirst : 1 / ((M : ℝ) * (6 + Real.log (M : ℝ)) ^ (3 / 2 : ℝ)) ≤
      (6 + Real.log (M : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = (1 / (M : ℝ)) * (6 + Real.log (M : ℝ)) ^ (-(3 / 2 : ℝ)) := by
        rw [Real.rpow_neg hL.le]
        simp only [one_div, mul_inv_rev]
        ring
      _ ≤ 1 * (6 + Real.log (M : ℝ)) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul (by simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hM1))
          (Real.rpow_le_rpow_of_exponent_le (by linarith [Real.log_nonneg hM1]) (by norm_num))
          (Real.rpow_nonneg hL.le _) (by norm_num)
      _ = _ := one_mul _
  have hs := (summable_nat_add_iff M).mpr summable_shifted_log_threeHalves
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.zero_add]
  have hshift : (fun k : ℕ =>
      1 / (((k + 1 + M : ℕ) : ℝ) *
        (6 + Real.log ((k + 1 + M : ℕ) : ℝ)) ^ (3 / 2 : ℝ))) =
      (fun k : ℕ => 1 / (((k + M + 1 : ℕ) : ℝ) *
        (6 + Real.log ((k + M + 1 : ℕ) : ℝ)) ^ (3 / 2 : ℝ))) := by
    funext k
    simp only [Nat.add_assoc, Nat.add_comm]
  rw [hshift]
  linarith

end RiemannResearch.Analysis
