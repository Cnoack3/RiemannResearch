/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Time-trapezoid estimates for the Montgomery prime energy

The intended arithmetic input is the averaged sieve in Languasco–Perelli–Zaccagnini,
Lemma 6 and (2.14), https://doi.org/10.1090/tran/6835 . The finite shell estimate
keeps its coefficient-mass bound explicit. -/

open MeasureTheory
namespace RiemannResearch.Analysis.MontgomeryHorizontalTransfer

/-- Exact integral of the three pieces of the Fourier majorant for a time
trapezoid. For `w ≤ T` the cuts are in increasing order. -/
theorem trapezoidFrequencyEnvelope_integral {T w : ℝ} (hT : 0 < T) (hw : 0 < w) :
    (∫ _ : ℝ in (0 : ℝ)..(1 / T), T) +
      (∫ s : ℝ in (1 / T)..(1 / w), 1 / s) +
      (1 / w) * (∫ s : ℝ in Set.Ioi (1 / w), s ^ (-2 : ℝ)) =
      2 + Real.log (T / w) := by
  have ht : 0 < 1 / T := by positivity
  have hw' : 0 < 1 / w := by positivity
  have hratio : (1 / w) / (1 / T) = T / w := by field_simp
  rw [intervalIntegral.integral_const, integral_one_div_of_pos ht hw', hratio,
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hw']
  norm_num [Real.rpow_neg_one, smul_eq_mul]
  <;> field_simp
  <;> ring

/-- Bound one shell of the off-diagonal Fourier expansion from its
nonnegative coefficient mass and a uniform bound on the kernel. -/
theorem trapezoidGapShell_le {ι : Type*} (shell : Finset ι) {a k : ι → ℝ}
    {B C : ℝ} (hB : 0 ≤ B) (ha : ∀ i ∈ shell, 0 ≤ a i)
    (hk : ∀ i ∈ shell, |k i| ≤ B) (hMass : ∑ i ∈ shell, a i ≤ C) :
    |∑ i ∈ shell, a i * k i| ≤ B * C := by
  calc
    _ ≤ ∑ i ∈ shell, |a i * k i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ shell, B * a i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (ha i hi), mul_comm B]
      exact mul_le_mul_of_nonneg_left (hk i hi) (ha i hi)
    _ = B * ∑ i ∈ shell, a i := (Finset.mul_sum _ _ _).symm
    _ ≤ B * C := mul_le_mul_of_nonneg_left hMass hB

end RiemannResearch.Analysis.MontgomeryHorizontalTransfer
