import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Cancellation-preserving Abel multipliers

Source: algebraic continuation of the user-provided handoff and
`DyadicBoundaryFourierResearchNote20260910.md`, September 10, 2026.
These declarations control the complete elementary multiplier. They do not
identify the actual signed arithmetic boundary coefficients with a Fourier
series, or supply the remaining uniform arithmetic square-sum estimate.
-/

namespace RiemannResearch.Analysis
open scoped BigOperators
noncomputable section

/-- The numerator retains the cancellation of the small Abel denominator. -/
def abelCancellationMultiplier (q : ℝ) (z : ℂ) : ℂ :=
  (1 - z) / (1 - (q : ℂ) * z)

/-- Exact identity, including the defect away from the unit circle. -/
theorem abel_norm_sq_identity_general (q : ℝ) (z : ℂ) :
    ‖1 - (q : ℂ) * z‖ ^ 2 =
      (1 - q) ^ 2 + q * ‖1 - z‖ ^ 2 + q * (q - 1) * (‖z‖ ^ 2 - 1) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Complete numerator/denominator cancellation on the unit circle. -/
theorem abel_norm_sq_identity (q : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1 - (q : ℂ) * z‖ ^ 2 = (1 - q) ^ 2 + q * ‖1 - z‖ ^ 2 := by
  simpa only [hz, one_pow, sub_self, mul_zero, add_zero] using
    abel_norm_sq_identity_general q z

/-- Positive damping keeps the complete Abel denominator nonzero. -/
theorem abel_denominator_norm_pos (q : ℝ) (z : ℂ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hz : ‖z‖ = 1) :
    0 < ‖1 - (q : ℂ) * z‖ := by
  have hid := abel_norm_sq_identity q z hz
  have hpos : 0 < (1 - q) ^ 2 := sq_pos_of_pos (by linarith)
  have hnonneg := mul_nonneg hq0 (sq_nonneg ‖1 - z‖)
  have hn := norm_nonneg (1 - (q : ℂ) * z)
  nlinarith

/-- The earlier q-weighted estimate, retaining the exact signed quotient. -/
theorem abelCancellationMultiplier_weighted_sq_le_one (q : ℝ) (z : ℂ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hz : ‖z‖ = 1) :
    q * ‖abelCancellationMultiplier q z‖ ^ 2 ≤ 1 := by
  have hid := abel_norm_sq_identity q z hz
  have hd := abel_denominator_norm_pos q z hq0 hq1 hz
  rw [abelCancellationMultiplier, norm_div, div_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).2
  nlinarith [sq_nonneg (1 - q)]

/-- The sharp bound is uniformly at most two even when q approaches zero. -/
theorem abelCancellationMultiplier_norm_le_sharp (q : ℝ) (z : ℂ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hz : ‖z‖ = 1) :
    ‖abelCancellationMultiplier q z‖ ≤ 2 / (1 + q) := by
  have hid := abel_norm_sq_identity q z hz
  have hd := abel_denominator_norm_pos q z hq0 hq1 hz
  have hqp : 0 < 1 + q := by linarith
  have hx : ‖1 - z‖ ≤ 2 := by
    simpa only [norm_one, hz, show (1 : ℝ)+1 = 2 by norm_num] using norm_sub_le (1 : ℂ) z
  have hx0 := norm_nonneg (1 - z)
  have hx2 : ‖1 - z‖ ^ 2 ≤ 4 := by nlinarith
  have hprod := mul_nonneg (sq_nonneg (1 - q)) (sub_nonneg.mpr hx2)
  have hsq : ((1 + q) * ‖1 - z‖) ^ 2 ≤
      (2 * ‖1 - (q : ℂ) * z‖) ^ 2 := by
    nlinarith [hid]
  have hlinear : (1 + q) * ‖1 - z‖ ≤ 2 * ‖1 - (q : ℂ) * z‖ :=
    (sq_le_sq₀ (mul_nonneg hqp.le hx0) (by positivity)).mp hsq
  unfold abelCancellationMultiplier
  rw [norm_div]
  exact (div_le_div_iff₀ hd hqp).2 (by nlinarith)

/-- An absolute bound for every damping parameter in the admissible range. -/
theorem abelCancellationMultiplier_norm_le_two (q : ℝ) (z : ℂ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hz : ‖z‖ = 1) :
    ‖abelCancellationMultiplier q z‖ ≤ 2 := by
  refine (abelCancellationMultiplier_norm_le_sharp q z hq0 hq1 hz).trans ?_
  apply (div_le_iff₀ (by linarith : 0 < 1 + q)).2
  linarith

/-- The sharp estimate is attained at the antipodal unit-circle point. -/
theorem abelCancellationMultiplier_norm_neg_one (q : ℝ) (hq0 : 0 ≤ q) :
    ‖abelCancellationMultiplier q (-1)‖ = 2 / (1 + q) := by
  have hd : (1 : ℂ) - (q : ℂ) * (-1) = ((1 + q : ℝ) : ℂ) := by
    push_cast
    ring
  unfold abelCancellationMultiplier
  rw [norm_div, hd]
  have hn : (1 : ℂ) - (-1) = (2 : ℂ) := by ring
  rw [hn]
  have hdNorm : ‖((1+q : ℝ) : ℂ)‖ = 1+q := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1+q)]
  rw [hdNorm]
  norm_num

/-- Exact combination of the main Fourier factor and comparison factor.
This is algebra; an identification with actual arithmetic coefficients is separate. -/
theorem abelCancellationMultiplier_comparison_identity
    (q : ℝ) (z M : ℂ) (hd : 1 - (q : ℂ) * z ≠ 0) :
    M * abelCancellationMultiplier q z +
      (1 - (q : ℂ)) * z / (1 - (q : ℂ) * z) =
      1 + (M - 1) * abelCancellationMultiplier q z := by
  unfold abelCancellationMultiplier
  have hd' : 1 - z * (q : ℂ) ≠ 0 := by simpa only [mul_comm] using hd
  field_simp [hd, hd']
  <;> ring

/-- The mean term cancels only together with the complete finite Fourier sum. -/
theorem abelCancellationMultiplier_finite_mean_cancellation
    {ι : Type*} (S : Finset ι) (q : ℝ) (c0 : ℂ) (c z M : ι → ℂ)
    (hd : ∀ i ∈ S, 1 - (q : ℂ) * z i ≠ 0)
    (hmean : c0 + ∑ i ∈ S, c i = 0) :
    c0 + ∑ i ∈ S, c i *
      (M i * abelCancellationMultiplier q (z i) +
        (1 - (q : ℂ)) * z i / (1 - (q : ℂ) * z i)) =
      ∑ i ∈ S, c i * (M i - 1) * abelCancellationMultiplier q (z i) := by
  have hterm : ∀ i ∈ S,
      c i * (M i * abelCancellationMultiplier q (z i) +
        (1 - (q : ℂ)) * z i / (1 - (q : ℂ) * z i)) =
      c i + c i * (M i - 1) * abelCancellationMultiplier q (z i) := by
    intro i hi
    rw [abelCancellationMultiplier_comparison_identity q (z i) (M i) (hd i hi)]
    ring
  calc
    _ = c0 + ((∑ i ∈ S, c i) +
        ∑ i ∈ S, c i * (M i - 1) * abelCancellationMultiplier q (z i)) := by
      congr 1
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hterm
    _ = _ := by rw [← add_assoc, hmean, zero_add]

/-- Weighted diagonal finite energy bound for the complete input coefficient.
The input `v i` may itself contain any signed or mixed arithmetic expression.
This statement does not remove cross terms in a boundary/Fourier Gram matrix. -/
theorem abelCancellationMultiplier_finite_energy_le
    {ι : Type*} (S : Finset ι) (q : ℝ) (z v : ι → ℂ) (w : ι → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hz : ∀ i ∈ S, ‖z i‖ = 1) (hw : ∀ i ∈ S, 0 ≤ w i) :
    ∑ i ∈ S, w i * ‖v i * abelCancellationMultiplier q (z i)‖ ^ 2 ≤
      4 * ∑ i ∈ S, w i * ‖v i‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hb := abelCancellationMultiplier_norm_le_two q (z i) hq0 hq1 (hz i hi)
  have hm0 := norm_nonneg (abelCancellationMultiplier q (z i))
  have hm2 : ‖abelCancellationMultiplier q (z i)‖ ^ 2 ≤ 4 := by nlinarith
  rw [norm_mul, mul_pow]
  calc
    _ ≤ w i * (‖v i‖ ^ 2 * 4) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm2 (sq_nonneg _)) (hw i hi)
    _ = _ := by ring

end
end RiemannResearch.Analysis
