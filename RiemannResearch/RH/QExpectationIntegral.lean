import RiemannResearch.RH.QDivisibilityResidueCoefficients
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The actual Q integral and inverse-square arithmetic expectations

Source: user-provided Q-law and finite inclusion-exclusion program,
13 October 2026. Countable Bochner integration identifies the previously
computed weighted series with the actual probability measure Q. Bounds
for every finite divisibility combination discharge integrability.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoProbability

/-- Every bounded arithmetic observable is in every finite-Q Lp space. -/
theorem memLp_Q_of_bounded (f : ℕ → ℝ) {C : ℝ} (hf : ∀ n, |f n| ≤ C)
    (p : ℝ≥0∞) : MemLp (fun k : ℕ+ => f (k : ℕ)) p Q := by
  apply MemLp.of_bound StronglyMeasurable.of_discrete.aestronglyMeasurable C
  apply Filter.Eventually.of_forall
  intro k
  simpa only [Real.norm_eq_abs] using hf (k : ℕ)

theorem integrable_Q_of_bounded (f : ℕ → ℝ) {C : ℝ} (hf : ∀ n, |f n| ≤ C) :
    Integrable (fun k : ℕ+ => f (k : ℕ)) Q :=
  memLp_one_iff_integrable.mp (memLp_Q_of_bounded f hf 1)

/-- Exact equality with the actual probability integral, for every
integrable observable. The mass at every positive integer is retained. -/
theorem inversePowerMean_zero_eq_integral_of_integrable (f : ℕ → ℝ)
    (hf : Integrable (fun k : ℕ+ => f (k : ℕ)) Q) :
    inversePowerMean 0 f = ∫ k : ℕ+, f (k : ℕ) ∂Q := by
  rw [inversePowerMean_zero_eq_pnat_tsum, integral_countable hf]
  apply tsum_congr
  intro k
  rw [measureReal_def, ZetaTwoProbability.measure_singleton]
  rw [ENNReal.toReal_ofReal (show 0 ≤ 1 / (zetaTwo * (k : ℝ)^2) from
    positiveQWeight_nonneg (k : ℕ))]
  rfl

/-- Bounded-observable version with no remaining integrability hypothesis. -/
theorem inversePowerMean_zero_eq_integral (f : ℕ → ℝ) {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) :
    inversePowerMean 0 f = ∫ k : ℕ+, f (k : ℕ) ∂Q :=
  inversePowerMean_zero_eq_integral_of_integrable f (integrable_Q_of_bounded f hf)

/-- Every signed finite incidence sum has an explicit uniform bound. -/
theorem qScaledDivisibilitySum_abs_le (S : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) :
    |qScaledDivisibilitySum S a n| ≤ ∑ k ∈ S, |a k * (k : ℝ)^2| := by
  unfold qScaledDivisibilitySum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  by_cases hkn : k ∣ n
  · simp only [if_pos hkn, mul_one, le_refl]
  · simp only [if_neg hkn, mul_zero, abs_zero]
    exact abs_nonneg _

/-- The complete divisor wavelet is bounded uniformly over all integers. -/
theorem qDivisorWavelet_abs_le (r n : ℕ) :
    |qDivisorWavelet r n| ≤
      ∑ k ∈ r.divisors, |(ArithmeticFunction.moebius (r / k) : ℝ) * (k : ℝ)^2| :=
  qScaledDivisibilitySum_abs_le r.divisors
    (fun k => (ArithmeticFunction.moebius (r / k) : ℝ)) n

/-- In particular the actual Möbius wavelets are genuine Q-L2 observables. -/
theorem memLp_qDivisorWavelet (r : ℕ) (p : ℝ≥0∞) :
    MemLp (fun k : ℕ+ => qDivisorWavelet r (k : ℕ)) p Q :=
  memLp_Q_of_bounded (qDivisorWavelet r) (qDivisorWavelet_abs_le r) p

end RiemannResearch.RH.ZetaTwoHilbert
