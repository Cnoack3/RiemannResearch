import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! # Finite first-harmonic estimates for nonnegative counts -/

open scoped BigOperators

namespace RiemannResearch.Analysis.FirstHarmonicCounts

/-- The signed row error has a fixed sign at every height and every frequency. -/
theorem row_sub_sin_nonneg {t k : ℝ} (ht : 0 < t) (hk : 0 ≤ k) :
    0 ≤ k - Real.sin (t * k) / t := by
  apply sub_nonneg.mpr
  apply (div_le_iff₀ ht).mpr
  simpa [mul_comm] using Real.sin_le (mul_nonneg ht.le hk)

/-- Global cubic Taylor estimate in row-count units. -/
theorem row_sub_sin_le_cube {t k : ℝ} (ht : 0 < t) (hk : 0 ≤ k) :
    k - Real.sin (t * k) / t ≤ (t ^ 2 / 6) * k ^ 3 := by
  have h := Real.sin_ge_sub_cube (mul_nonneg ht.le hk)
  calc
    k - Real.sin (t * k) / t = (t * k - Real.sin (t * k)) / t := by
      field_simp [ht.ne'] <;> ring
    _ ≤ ((t * k) ^ 3 / 6) / t := div_le_div_of_nonneg_right (by linarith) ht.le
    _ = (t ^ 2 / 6) * k ^ 3 := by field_simp [ht.ne'] <;> ring

private theorem sub_sin_le_half_sq {x : ℝ} (hx : 0 ≤ x) :
    x - Real.sin x ≤ x ^ 2 / 2 := by
  by_cases h : x ≤ 3
  · have hpow := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h)
    nlinarith [Real.sin_ge_sub_cube hx]
  · have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_ge h))
        (show 0 ≤ x + 1 by linarith)
    nlinarith [Real.neg_one_le_sin x]

/-- The second moment already suffices to control the first harmonic. -/
theorem row_sub_sin_le_sq {t k : ℝ} (ht : 0 < t) (hk : 0 ≤ k) :
    k - Real.sin (t * k) / t ≤ (t / 2) * k ^ 2 := by
  calc
    k - Real.sin (t * k) / t = (t * k - Real.sin (t * k)) / t := by
      field_simp [ht.ne'] <;> ring
    _ ≤ ((t * k) ^ 2 / 2) / t :=
      div_le_div_of_nonneg_right (sub_sin_le_half_sq (mul_nonneg ht.le hk)) ht.le
    _ = (t / 2) * k ^ 2 := by field_simp [ht.ne'] <;> ring

private theorem abs_sum_sub_sin_le_of_rows {ι : Type*} (s : Finset ι)
    (K : ι → ℝ) {t a : ℝ} (ht : 0 < t) (hK : ∀ i ∈ s, 0 ≤ K i)
    (p : ℕ) (hrow : ∀ i ∈ s, K i - Real.sin (t * K i) / t ≤ a * K i ^ p) :
    |(∑ i ∈ s, K i) - ∑ i ∈ s, Real.sin (t * K i) / t| ≤
      a * ∑ i ∈ s, K i ^ p := by
  rw [← Finset.sum_sub_distrib, abs_of_nonneg (Finset.sum_nonneg
    (fun i hi => row_sub_sin_nonneg ht (hK i hi))), Finset.mul_sum]
  exact Finset.sum_le_sum hrow

/-- First-harmonic recovery with the sharp cubic Taylor coefficient. -/
theorem abs_sum_sub_sin_le_third_moment {ι : Type*} (s : Finset ι)
    (K : ι → ℝ) {t : ℝ} (ht : 0 < t) (hK : ∀ i ∈ s, 0 ≤ K i) :
    |(∑ i ∈ s, K i) - ∑ i ∈ s, Real.sin (t * K i) / t| ≤
      (t ^ 2 / 6) * ∑ i ∈ s, K i ^ 3 :=
  abs_sum_sub_sin_le_of_rows s K ht hK 3 fun i hi => row_sub_sin_le_cube ht (hK i hi)

/-- First-harmonic recovery under second-moment control alone. -/
theorem abs_sum_sub_sin_le_second_moment {ι : Type*} (s : Finset ι)
    (K : ι → ℝ) {t : ℝ} (ht : 0 < t) (hK : ∀ i ∈ s, 0 ≤ K i) :
    |(∑ i ∈ s, K i) - ∑ i ∈ s, Real.sin (t * K i) / t| ≤
      (t / 2) * ∑ i ∈ s, K i ^ 2 :=
  abs_sum_sub_sin_le_of_rows s K ht hK 2 fun i hi => row_sub_sin_le_sq ht (hK i hi)

end RiemannResearch.Analysis.FirstHarmonicCounts
