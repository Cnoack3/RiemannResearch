/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Total variance after conditioning on reflection pairs

Source: user-provided argument, 11 September 2026.

This finite algebraic module does not assume that the weights are normalized.
Its squared-error identity becomes the law of total variance when the center
is the global mean and the weights have total mass one.  The reflection
identity supplies an explicit within-pair energy, without deleting signed
cross terms from any representation of the values.
-/

open scoped BigOperators

namespace FinitePairVariance

noncomputable section

/-- Mean conditional on one two-point pair. -/
def pairMean (u v x y : ℝ) : ℝ := (u * x + v * y) / (u + v)

/-- The two-point conditional squared-error decomposition. -/
theorem weighted_sq_decomposition (u v x y a : ℝ)
    (hu : 0 < u) (hv : 0 < v) :
    u * (x - a) ^ 2 + v * (y - a) ^ 2 =
      (u + v) * (pairMean u v x y - a) ^ 2 +
        u * v / (u + v) * (x - y) ^ 2 := by
  unfold pairMean
  field_simp [ne_of_gt (add_pos hu hv)]
  <;> ring

/-- Reflection expresses the conditional mean in one centered coordinate. -/
theorem pairMean_of_reflection (u v x y C : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hxy : x + y = C) :
    pairMean u v x y = C / 2 + (u - v) / (u + v) * (x - C / 2) := by
  rw [← hxy]
  unfold pairMean
  field_simp [ne_of_gt (add_pos hu hv)]
  <;> ring

/-- The reflected conditional variance has the coefficient `4uv/(u+v)`. -/
theorem weighted_reflection_decomposition (u v x y a C : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hxy : x + y = C) :
    u * (x - a) ^ 2 + v * (y - a) ^ 2 =
      (u + v) * (pairMean u v x y - a) ^ 2 +
        (4 * u * v / (u + v)) * (x - C / 2) ^ 2 := by
  rw [weighted_sq_decomposition u v x y a hu hv]
  congr 1
  rw [← hxy]
  ring

/-- Bounding the weight of just one member bounds the within-pair coefficient. -/
theorem reflection_coefficient_le (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    4 * u * v / (u + v) ≤ 4 * v := by
  apply (div_le_iff₀ (add_pos hu hv)).2
  nlinarith [sq_nonneg v]

theorem reflection_coefficient_le_left (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    4 * u * v / (u + v) ≤ 4 * u := by
  apply (div_le_iff₀ (add_pos hu hv)).2
  nlinarith [sq_nonneg u]

theorem reflection_coefficient_le_min (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    4 * u * v / (u + v) ≤ 4 * min u v := by
  rcases le_total u v with h | h
  · rw [min_eq_left h]
    exact reflection_coefficient_le_left u v hu hv
  · rw [min_eq_right h]
    exact reflection_coefficient_le u v hu hv

/-- Either member of the pair can supply the small-weight bound. -/
theorem reflection_coefficient_le_of_or (u v B : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hB : u ≤ B ∨ v ≤ B) :
    4 * u * v / (u + v) ≤ 4 * B := by
  rcases hB with hB | hB
  · exact (reflection_coefficient_le_left u v hu hv).trans
      (mul_le_mul_of_nonneg_left hB (by norm_num))
  · exact (reflection_coefficient_le u v hu hv).trans
      (mul_le_mul_of_nonneg_left hB (by norm_num))

variable {ι : Type*}

/-- Weighted squared error before conditioning. -/
def fullError (s : Finset ι) (u v x y : ι → ℝ) (a : ℝ) : ℝ :=
  ∑ r ∈ s, (u r * (x r - a) ^ 2 + v r * (y r - a) ^ 2)

/-- Error in the means conditional on the pair. -/
def calibration (s : Finset ι) (u v x y : ι → ℝ) (a : ℝ) : ℝ :=
  ∑ r ∈ s, (u r + v r) * (pairMean (u r) (v r) (x r) (y r) - a) ^ 2

/-- Expected within-pair variance when the two values sum to `C`. -/
def noise (s : Finset ι) (u v x : ι → ℝ) (C : ℝ) : ℝ :=
  ∑ r ∈ s, (4 * u r * v r / (u r + v r)) * (x r - C / 2) ^ 2

/-- Exact finite total variance, in squared-error form. -/
theorem fullError_eq_calibration_add_noise
    (s : Finset ι) (u v x y : ι → ℝ) (a C : ℝ)
    (hu : ∀ r ∈ s, 0 < u r) (hv : ∀ r ∈ s, 0 < v r)
    (hxy : ∀ r ∈ s, x r + y r = C) :
    fullError s u v x y a = calibration s u v x y a + noise s u v x C := by
  unfold fullError calibration noise
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r hr =>
    weighted_reflection_decomposition (u r) (v r) (x r) (y r) a C
      (hu r hr) (hv r hr) (hxy r hr)

theorem noise_nonneg (s : Finset ι) (u v x : ι → ℝ) (C : ℝ)
    (hu : ∀ r ∈ s, 0 < u r) (hv : ∀ r ∈ s, 0 < v r) :
    0 ≤ noise s u v x C := by
  apply Finset.sum_nonneg
  intro r hr
  have hru := hu r hr
  have hrv := hv r hr
  exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (sq_nonneg _)

theorem calibration_nonneg (s : Finset ι) (u v x y : ι → ℝ) (a : ℝ)
    (hu : ∀ r ∈ s, 0 < u r) (hv : ∀ r ∈ s, 0 < v r) :
    0 ≤ calibration s u v x y a := by
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg (le_of_lt (add_pos (hu r hr) (hv r hr))) (sq_nonneg _)

theorem calibration_le_fullError
    (s : Finset ι) (u v x y : ι → ℝ) (a C : ℝ)
    (hu : ∀ r ∈ s, 0 < u r) (hv : ∀ r ∈ s, 0 < v r)
    (hxy : ∀ r ∈ s, x r + y r = C) :
    calibration s u v x y a ≤ fullError s u v x y a := by
  rw [fullError_eq_calibration_add_noise s u v x y a C hu hv hxy]
  exact le_add_of_nonneg_right (noise_nonneg s u v x C hu hv)

/-- The noise is bounded by the unweighted centered energy of one half-period. -/
theorem noise_le_four_mul
    (s : Finset ι) (u v x : ι → ℝ) (C B : ℝ)
    (hu : ∀ r ∈ s, 0 < u r) (hv : ∀ r ∈ s, 0 < v r)
    (hvB : ∀ r ∈ s, v r ≤ B) :
    noise s u v x C ≤ 4 * B * ∑ r ∈ s, (x r - C / 2) ^ 2 := by
  unfold noise
  calc
    _ ≤ ∑ r ∈ s, (4 * B) * (x r - C / 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact (reflection_coefficient_le (u r) (v r) (hu r hr) (hv r hr)).trans
        (mul_le_mul_of_nonneg_left (hvB r hr) (by norm_num))
    _ = _ := by rw [Finset.mul_sum]

theorem noise_le_four_mul_of_or
    (s : Finset ι) (u v x : ι → ℝ) (C B : ℝ)
    (hu : ∀ r ∈ s, 0 < u r) (hv : ∀ r ∈ s, 0 < v r)
    (hB : ∀ r ∈ s, u r ≤ B ∨ v r ≤ B) :
    noise s u v x C ≤ 4 * B * ∑ r ∈ s, (x r - C / 2) ^ 2 := by
  unfold noise
  calc
    _ ≤ ∑ r ∈ s, (4 * B) * (x r - C / 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_right
        (reflection_coefficient_le_of_or (u r) (v r) B (hu r hr) (hv r hr) (hB r hr))
        (sq_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

theorem fullError_le_calibration_add_four_mul
    (s : Finset ι) (u v x y : ι → ℝ) (a C B : ℝ)
    (hu : ∀ r ∈ s, 0 < u r) (hv : ∀ r ∈ s, 0 < v r)
    (hxy : ∀ r ∈ s, x r + y r = C) (hvB : ∀ r ∈ s, v r ≤ B) :
    fullError s u v x y a ≤ calibration s u v x y a +
      4 * B * ∑ r ∈ s, (x r - C / 2) ^ 2 := by
  rw [fullError_eq_calibration_add_noise s u v x y a C hu hv hxy]
  exact add_le_add le_rfl (noise_le_four_mul s u v x C B hu hv hvB)

/-- A common lower weight controls the uniform centered energy. -/
theorem centered_energy_le_fullError
    (s : Finset ι) (u v x y : ι → ℝ) (a C c : ℝ)
    (hc : 0 ≤ c) (hcu : ∀ r ∈ s, c ≤ u r) (hcv : ∀ r ∈ s, c ≤ v r)
    (hxy : ∀ r ∈ s, x r + y r = C) :
    2 * c * ∑ r ∈ s, (x r - C / 2) ^ 2 ≤ fullError s u v x y a := by
  unfold fullError
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hu' := mul_le_mul_of_nonneg_right (hcu r hr) (sq_nonneg (x r - a))
  have hv' := mul_le_mul_of_nonneg_right (hcv r hr) (sq_nonneg (y r - a))
  have hpar : c * ((x r - a) ^ 2 + (y r - a) ^ 2) =
      2 * c * (x r - C / 2) ^ 2 + 2 * c * (C / 2 - a) ^ 2 := by
    rw [← hxy r hr]
    ring
  have hc' := mul_nonneg hc (sq_nonneg (C / 2 - a))
  nlinarith

end
end FinitePairVariance
