import RiemannResearch.RH.ParetoCompressedMellinCosine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Summability of the actual compressed-Mellin cosine series

Source: user-provided `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`,
Section 3.1.  The summability majorant below is an elementary multiple of the
actual Pareto probability mass. No p-series, smooth-gap or RH input is assumed.
-/

namespace RiemannResearch.RH.Pareto.CompressedMellin
noncomputable section
open scoped BigOperators

/-- Elementary quadratic cosine estimate, derived from the sine bound. -/
theorem one_sub_cos_le_half_square (x : ℝ) :
    1 - Real.cos x ≤ x ^ 2 / 2 := by
  have hs : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  have hsquare := Real.sin_sq_add_cos_sq (x / 2)
  have hdouble := Real.cos_two_mul (x / 2)
  have hhalf : 2 * (x / 2) = x := by ring
  rw [hhalf] at hdouble
  have hsq : Real.sin (x / 2) ^ 2 ≤ (x / 2) ^ 2 := by
    nlinarith [sq_abs (Real.sin (x / 2)), sq_abs (x / 2),
      abs_nonneg (Real.sin (x / 2)), abs_nonneg (x / 2)]
  nlinarith

/-- Each genuine logarithmic cosine defect is dominated by the actual weight.
The estimate is deliberately coarse; the sharp frequency asymptotic is separate. -/
theorem cosineDeficit_le_weight (t : ℝ) (n : ℕ) :
    cosineDeficit t n ≤ t ^ 2 * paretoWeight n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hk : 0 < (n : ℝ) + 1 := by positivity
  have hlogpos : 0 ≤ Real.log (1 + 1 / ((n : ℝ) + 1)) :=
    Real.log_nonneg (le_add_of_nonneg_right (one_div_nonneg.mpr hk.le))
  have hlog : Real.log (1 + 1 / ((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 1) := by
    have h := Real.log_le_sub_one_of_pos
      (by positivity : 0 < 1 + 1 / ((n : ℝ) + 1))
    linarith
  have hlogsq : Real.log (1 + 1 / ((n : ℝ) + 1)) ^ 2 ≤
      (1 / ((n : ℝ) + 1)) ^ 2 := by
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hk.le]
  have hcompare : (1 / ((n : ℝ) + 1)) ^ 2 / 2 ≤ paretoWeight n := by
    have hp : 0 < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
    have hpoly : ((n : ℝ) + 1) * ((n : ℝ) + 2) ≤
        2 * ((n : ℝ) + 1) ^ 2 := by nlinarith
    calc
      _ = 1 / (2 * ((n : ℝ) + 1) ^ 2) := by
        field_simp [ne_of_gt hk]
        <;> ring
      _ ≤ 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) :=
        one_div_le_one_div_of_le hp hpoly
      _ = paretoWeight n := by rfl
  have hm := mul_le_mul_of_nonneg_left hlogsq (sq_nonneg t)
  have hc := one_sub_cos_le_half_square
    (t * Real.log (1 + 1 / ((n : ℝ) + 1)))
  unfold cosineDeficit
  calc
    _ ≤ t ^ 2 * Real.log (1 + 1 / ((n : ℝ) + 1)) ^ 2 / 2 := by
      simpa only [mul_pow] using hc
    _ ≤ t ^ 2 * (1 / ((n : ℝ) + 1)) ^ 2 / 2 := by linarith
    _ = t ^ 2 * ((1 / ((n : ℝ) + 1)) ^ 2 / 2) := by ring
    _ ≤ t ^ 2 * paretoWeight n :=
      mul_le_mul_of_nonneg_left hcompare (sq_nonneg t)

/-- Unconditional convergence of the full, actual cosine-deficit series. -/
theorem cosineDeficit_summable (t : ℝ) : Summable (cosineDeficit t) :=
  Summable.of_nonneg_of_le (cosineDeficit_nonneg t) (cosineDeficit_le_weight t)
    (paretoWeight_hasSum.summable.mul_left (t ^ 2))

theorem cosineDeficit_tsum_le (t : ℝ) :
    (∑' n, cosineDeficit t n) ≤ t ^ 2 := by
  have h := (cosineDeficit_summable t).tsum_le_tsum (cosineDeficit_le_weight t)
    (paretoWeight_hasSum.summable.mul_left (t ^ 2))
  simpa only [tsum_mul_left, paretoWeight_tsum, mul_one] using h

theorem cosineMass_le_quadratic (t : ℝ) : cosineMass t ≤ 1 + 2 * t ^ 2 := by
  unfold cosineMass
  linarith [cosineDeficit_tsum_le t]

/-- The full exact density identity now has no summability hypothesis. -/
theorem tsum_cellDensity_unconditional (t : ℝ) :
    ∑' n, cellDensity t n = cosineMass t :=
  tsum_cellDensity t (cosineDeficit_summable t)

end
end RiemannResearch.RH.Pareto.CompressedMellin
