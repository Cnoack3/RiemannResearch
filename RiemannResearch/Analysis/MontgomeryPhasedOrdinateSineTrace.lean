import RiemannResearch.Analysis.MontgomeryOrdinateSineTrace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Phase shifts and a two-sided frequency envelope for the actual
ordinate-window sine trace. The zero frequency contributes exactly zero. -/

noncomputable section

open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.Analysis.MontgomeryOrdinateSineTrace

/-- A phase parameter allows one dictionary to handle both sine and cosine
modes. Lean's real division convention gives the same formula at frequency zero. -/
theorem ordinate_phased_sine_increment_integral (γ h a θ : ℝ) :
    (∫ t in (γ - h)..γ, Real.sin ((t + h) * a + θ) - Real.sin (t * a + θ)) =
      2 * (1 - Real.cos (h * a)) * Real.cos (γ * a + θ) / a := by
  by_cases ha : a = 0
  · simp [ha]
  let δ := θ / a
  have hδ : δ * a = θ := div_mul_cancel₀ θ ha
  have hshift (t : ℝ) : (t + δ) * a = t * a + θ := by rw [add_mul, hδ]
  have hshifth (t : ℝ) : (t + δ + h) * a = (t + h) * a + θ := by
    rw [show t + δ + h = (t + h) + δ by ring, hshift]
  have hi := intervalIntegral.integral_comp_add_right (a := γ - h) (b := γ)
    (fun t : ℝ => Real.sin ((t + h) * a) - Real.sin (t * a)) δ
  simp only [hshifth, hshift] at hi
  rw [hi, show γ - h + δ = (γ + δ) - h by ring, ordinate_sine_increment_integral _ _ _ ha, hshift]

/-- Absolute window response simultaneously controls very small and very large
frequencies, uniformly in the phase, the sampled ordinate and the signed width. -/
theorem abs_ordinate_phased_sine_increment_integral_le (γ h a θ : ℝ) :
    |∫ t in (γ - h)..γ, Real.sin ((t + h) * a + θ) - Real.sin (t * a + θ)| ≤
      min (h ^ 2 * |a|) (4 / |a|) := by
  rw [ordinate_phased_sine_increment_integral]
  by_cases ha : a = 0
  · simp [ha]
  have hp := abs_pos.mpr ha
  have hcos := sub_nonneg.mpr (Real.cos_le_one (h * a))
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)), abs_of_nonneg hcos]
  have hmul := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (γ * a + θ))
    (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hcos)
  rw [mul_one] at hmul
  apply le_min
  · apply (div_le_iff₀ hp).2
    apply hmul.trans
    have hs := Real.abs_sin_le_abs (x := h * a / 2)
    have hs2 := mul_self_le_mul_self (abs_nonneg _) hs
    rw [← sq, ← sq, sq_abs, sq_abs] at hs2
    have hc := Real.cos_two_mul_eq_one_sub (h * a / 2)
    rw [show 2 * (h * a / 2) = h * a by ring] at hc
    rw [mul_assoc, ← sq, sq_abs]
    nlinarith only [hc, hs2]
  · apply div_le_div_of_nonneg_right _ hp.le
    exact hmul.trans (by linarith only [Real.neg_one_le_cos (h * a)])

/-- Linear combinations retain their individual phase shifts, including
zero frequencies. The identity also applies to signed weights. -/
theorem ordinate_weighted_phased_sine_increment_integral {ι : Type*} (s : Finset ι)
    (w a θ : ι → ℝ) (γ h : ℝ) :
    (∫ t in (γ - h)..γ, ∑ i ∈ s, w i *
      (Real.sin ((t + h) * a i + θ i) - Real.sin (t * a i + θ i))) =
        ∑ i ∈ s, w i * (2 * (1 - Real.cos (h * a i)) * Real.cos (γ * a i + θ i) / a i) := by
  have hc (i : ι) : Continuous (fun t : ℝ =>
      w i * (Real.sin ((t + h) * a i + θ i) - Real.sin (t * a i + θ i))) := by fun_prop
  rw [intervalIntegral.integral_finsetSum (fun i _ => (hc i).intervalIntegrable _ _)]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [intervalIntegral.integral_const_mul, ordinate_phased_sine_increment_integral])

end RiemannResearch.Analysis.MontgomeryOrdinateSineTrace
