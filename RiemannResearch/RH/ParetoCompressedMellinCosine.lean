import RiemannResearch.RH.ParetoWeights
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The exact cosine density of compressed Mellin duals

Source: user-provided `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`,
Section 3.1. The arithmetic functions below are the actual full-tail cosine
series. The identification with a bundled Mellin operator norm and the sharp
asymptotic require additional analytic proofs; they are not asserted here.
-/

namespace RiemannResearch.RH.Pareto.CompressedMellin
noncomputable section
open scoped BigOperators

/-- Exact real-coordinate square of the difference of two complex phases.
The signed mixed term is retained. -/
theorem phase_difference_square (a b x y : ℝ) :
    (a * Real.cos x - b * Real.cos y) ^ 2 +
      (a * Real.sin x - b * Real.sin y) ^ 2 =
    a ^ 2 + b ^ 2 - 2 * a * b * Real.cos (x - y) := by
  calc
    _ = a ^ 2 * (Real.cos x ^ 2 + Real.sin x ^ 2) +
        b ^ 2 * (Real.cos y ^ 2 + Real.sin y ^ 2) -
        2 * a * b * (Real.cos x * Real.cos y + Real.sin x * Real.sin y) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, Real.cos_sq_add_sin_sq, ← Real.cos_sub]; ring

/-- The integer coordinate is `n+1`, consistently with `paretoWeight n`. -/
def cosineDeficit (t : ℝ) (n : ℕ) : ℝ :=
  1 - Real.cos (t * Real.log (1 + 1 / ((n : ℝ) + 1)))

/-- Exact positive series in the report. Summability is separately required
when it is identified with the squared dual norm. -/
def cosineMass (t : ℝ) : ℝ := 1 + 2 * ∑' n, cosineDeficit t n

def cellDensity (t : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) / ((n : ℝ) + 1) +
  ((n : ℝ) + 1) / ((n : ℝ) + 2) -
  2 * Real.cos (t * Real.log (1 + 1 / ((n : ℝ) + 1)))

theorem cosineDeficit_nonneg (t : ℝ) (n : ℕ) : 0 ≤ cosineDeficit t n := by
  unfold cosineDeficit
  exact sub_nonneg.mpr (Real.cos_le_one _)

theorem cosineDeficit_le_two (t : ℝ) (n : ℕ) : cosineDeficit t n ≤ 2 := by
  unfold cosineDeficit
  linarith [Real.neg_one_le_cos (t * Real.log (1 + 1 / ((n : ℝ) + 1)))]

@[simp] theorem cosineDeficit_zero (n : ℕ) : cosineDeficit 0 n = 0 := by
  simp [cosineDeficit]

@[simp] theorem cosineDeficit_neg (t : ℝ) (n : ℕ) :
    cosineDeficit (-t) n = cosineDeficit t n := by
  simp [cosineDeficit, neg_mul, Real.cos_neg]

@[simp] theorem cosineMass_zero : cosineMass 0 = 1 := by
  simp [cosineMass]

@[simp] theorem cosineMass_neg (t : ℝ) : cosineMass (-t) = cosineMass t := by
  simp [cosineMass]

theorem cosineMass_ge_one (t : ℝ) : 1 ≤ cosineMass t := by
  have h : (0 : ℝ) ≤ ∑' n, cosineDeficit t n := tsum_nonneg (cosineDeficit_nonneg t)
  unfold cosineMass
  linarith

/-- Exact cell identity. The Pareto weight is retained rather than absorbed
into an asymptotic error. -/
theorem cellDensity_eq (t : ℝ) (n : ℕ) :
    cellDensity t n = paretoWeight n + 2 * cosineDeficit t n := by
  have hn₁ : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn₂ : (n : ℝ) + 2 ≠ 0 := by positivity
  unfold cellDensity cosineDeficit paretoWeight
  push_cast
  field_simp
  <;> ring

theorem cellDensity_nonneg (t : ℝ) (n : ℕ) : 0 ≤ cellDensity t n := by
  rw [cellDensity_eq]
  exact add_nonneg (paretoWeight_pos n).le (mul_nonneg (by norm_num) (cosineDeficit_nonneg t n))

/-- Finite truncations retain both the exact mass and the entire cosine head. -/
theorem sum_cellDensity (t : ℝ) (s : Finset ℕ) :
    ∑ n ∈ s, cellDensity t n =
      (∑ n ∈ s, paretoWeight n) + 2 * ∑ n ∈ s, cosineDeficit t n := by
  simp only [cellDensity_eq, Finset.sum_add_distrib, Finset.mul_sum]

/-- Full series assembly, conditional only on the explicitly stated
summability of the actual cosine deficits. -/
theorem tsum_cellDensity (t : ℝ) (hs : Summable (cosineDeficit t)) :
    ∑' n, cellDensity t n = cosineMass t := by
  simp only [cellDensity_eq]
  rw [Summable.tsum_add paretoWeight_hasSum.summable (hs.mul_left 2),
    tsum_mul_left, paretoWeight_tsum]
  rfl

end
end RiemannResearch.RH.Pareto.CompressedMellin
