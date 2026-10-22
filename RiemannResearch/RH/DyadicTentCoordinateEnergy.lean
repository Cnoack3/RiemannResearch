/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/

import RiemannResearch.RH.DyadicTentMellinCoefficients
import RiemannResearch.Analysis.IntegerTentSupport
import Mathlib.Analysis.PSeries


/-!
# Spatial control of the actual dyadic Mellin coefficient columns

Source: continuation of the user-provided FourierBridgeLeanVerification20260910(1).md.
The spatial majorant follows directly from the actual root-tent integral and
its height bound. Combined with the p-series theorem, it proves square
summability over boundary coordinates for each frequency, uniformly in the
frequency. This does not bound the full signed arithmetic Fourier energy;
no mixed terms are discarded or replaced by a diagonal expression.
-/

open MeasureTheory
namespace RiemannResearch.Analysis

theorem norm_integral_rootTent_fourier_kernel_le_spatial {a ω : ℝ}
    (ha : 0 < a) :
    ‖∫ x in a..a + 2,
      (rootTent a x : ℂ) * (x : ℂ) ^ (-Complex.I * (ω : ℂ) - 1)‖ ≤
        2 / a := by
  have hb : ∀ x ∈ Set.uIoc a (a + 2),
      ‖(rootTent a x : ℂ) * (x : ℂ) ^ (-Complex.I * (ω : ℂ) - 1)‖ ≤ a⁻¹ := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith : a ≤ a + 2)] at hx
    have hx0 : 0 < x := lt_trans ha hx.1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (rootTent_nonneg a x),
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-Complex.I * (ω : ℂ) - 1).re = -1 := by simp [Complex.mul_re]
    rw [hre, Real.rpow_neg_one]
    calc
      rootTent a x * x⁻¹ ≤ 1 * x⁻¹ :=
        mul_le_mul_of_nonneg_right (rootTent_le_one a x) (inv_nonneg.mpr hx0.le)
      _ ≤ a⁻¹ := by simpa using inv_anti₀ ha hx.1.le
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa [div_eq_mul_inv, mul_comm] using h

end RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
noncomputable section

theorem norm_dyadicTentMellinCoefficient_le_coordinate (i : ℕ) (h : ℤ) :
    ‖dyadicTentMellinCoefficient i h‖ ≤
      (Real.log 2)⁻¹ * ((i : ℝ) + 1)⁻¹ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [dyadicTentMellinCoefficient, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hlog]
  calc
    _ ≤ (Real.log 2)⁻¹ * (2 / (2 * (i + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (norm_integral_rootTent_fourier_kernel_le_spatial (by positivity))
        (inv_nonneg.mpr hlog.le)
    _ = _ := by congr 1; field_simp

theorem summable_sq_norm_dyadicTentMellinCoefficient_column (h : ℤ) :
    Summable (fun i : ℕ => ‖dyadicTentMellinCoefficient i h‖ ^ 2) := by
  have hp : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  apply (hp.mul_left ((Real.log 2)⁻¹ ^ 2)).of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have he := pow_le_pow_left₀ (norm_nonneg _) (norm_dyadicTentMellinCoefficient_le_coordinate i h) 2
  simpa only [mul_pow, inv_pow, one_div] using he

theorem tsum_sq_norm_dyadicTentMellinCoefficient_column_le (h : ℤ) :
    (∑' i : ℕ, ‖dyadicTentMellinCoefficient i h‖ ^ 2) ≤
      (Real.log 2)⁻¹ ^ 2 * (∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2) := by
  have hp : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    (summable_sq_norm_dyadicTentMellinCoefficient_column h) (hp.mul_left _)
  intro i
  have he := pow_le_pow_left₀ (norm_nonneg _) (norm_dyadicTentMellinCoefficient_le_coordinate i h) 2
  simpa only [mul_pow, inv_pow, one_div] using he

end
end RiemannResearch.RH.Pareto
