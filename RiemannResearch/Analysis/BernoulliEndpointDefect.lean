import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-!
# The signed endpoint defect of every even Bernoulli polynomial

The actual Mathlib Fourier series gives a nonnegative series of terms
`n^(-2m) * (1 - cos (2πnu))`.  Its sum is a positive scale times the
signed endpoint defect.  This proves the sign for every even order,
including strict positivity at the midpoint and the Bernoulli-number sign.

Source for the Fourier representation and proof strategy: NIST DLMF 24.8.1
(https://dlmf.nist.gov/24.8.E1), via Mathlib
`hasSum_one_div_nat_pow_mul_cos`.
-/

open Set
open scoped BigOperators

namespace RiemannResearch.Analysis

noncomputable section

/-- The endpoint defect is an actual convergent nonnegative Fourier series. -/
theorem hasSum_bernoulli_even_endpoint_defect (m : ℕ) (hm : 0 < m)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * m) *
      (1 - Real.cos (2 * Real.pi * (n : ℝ) * u)))
      ((2 * Real.pi) ^ (2 * m) / 2 / ((2 * m).factorial : ℝ) *
        ((-1 : ℝ) ^ (m + 1) * (bernoulliFun (2 * m) 0 - bernoulliFun (2 * m) u))) := by
  have h0 := hasSum_one_div_nat_pow_mul_cos (ne_of_gt hm)
    (x := (0 : ℝ)) (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  have hu' := hasSum_one_div_nat_pow_mul_cos (ne_of_gt hm) hu
  have hs := h0.sub hu'
  convert hs using 1 <;> try rfl
  · ext n
    simp only [mul_zero, Real.cos_zero]
    ring
  · unfold bernoulliFun
    ring

/-- The endpoint is an extremum of the correctly signed even Bernoulli
polynomial throughout the whole closed cell. -/
theorem bernoulli_even_endpoint_defect_nonneg (m : ℕ) (hm : 0 < m)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ (-1 : ℝ) ^ (m + 1) *
      (bernoulliFun (2 * m) 0 - bernoulliFun (2 * m) u) := by
  have hs := hasSum_bernoulli_even_endpoint_defect m hm hu
  have hsum : 0 ≤ (2 * Real.pi) ^ (2 * m) / 2 / ((2 * m).factorial : ℝ) *
      ((-1 : ℝ) ^ (m + 1) * (bernoulliFun (2 * m) 0 - bernoulliFun (2 * m) u)) := by
    rw [← hs.tsum_eq]
    exact tsum_nonneg (fun n => mul_nonneg (by positivity)
      (sub_nonneg.mpr (Real.cos_le_one _)))
  exact nonneg_of_mul_nonneg_right hsum (by positivity)

/-- The endpoint defect is strictly positive at the midpoint; its first
Fourier term is already strictly positive. -/
theorem bernoulli_even_endpoint_defect_half_pos (m : ℕ) (hm : 0 < m) :
    0 < (-1 : ℝ) ^ (m + 1) *
      (bernoulliFun (2 * m) 0 - bernoulliFun (2 * m) (1 / 2)) := by
  have hs := hasSum_bernoulli_even_endpoint_defect m hm
    (u := (1 / 2 : ℝ)) (by constructor <;> norm_num)
  have ht := hs.summable.tsum_pos
    (fun n => mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _)))
    1 (by
      norm_num only [Nat.cast_one, one_pow, div_one, one_mul, mul_one]
      rw [show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring,
        Real.cos_pi]
      norm_num)
  rw [hs.tsum_eq] at ht
  exact pos_of_mul_pos_right ht (by positivity)

/-- Every nonzero even Bernoulli number has its usual strict alternating sign. -/
theorem bernoulli_even_signed_pos (m : ℕ) (hm : 0 < m) :
    0 < (-1 : ℝ) ^ (m + 1) * (bernoulli (2 * m) : ℝ) := by
  have h0 := hasSum_one_div_nat_pow_mul_cos (ne_of_gt hm)
    (x := (0 : ℝ)) (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  have hs : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * m))
      ((2 * Real.pi) ^ (2 * m) / 2 / ((2 * m).factorial : ℝ) *
        ((-1 : ℝ) ^ (m + 1) * bernoulliFun (2 * m) 0)) := by
    convert h0 using 1 <;> try rfl
    · ext n
      simp only [mul_zero, Real.cos_zero, mul_one]
    · unfold bernoulliFun
      ring
  have ht := hs.summable.tsum_pos (fun n => by positivity) 1 (by norm_num)
  rw [hs.tsum_eq] at ht
  have h := pos_of_mul_pos_right ht (show 0 ≤
    (2 * Real.pi) ^ (2 * m) / 2 / ((2 * m).factorial : ℝ) by positivity)
  rwa [bernoulliFun_eval_zero] at h

end

end RiemannResearch.Analysis
