import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! The real integral contributed by a single occurrence to the covariance
of a forward counting window with a finite sine polynomial. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.Analysis.MontgomeryOrdinateSineTrace

/-- Integrating a sine increment over the origins whose window contains
one ordinate gives this exact cosine weight, at either sign of the frequency. -/
theorem ordinate_sine_increment_integral (γ h a : ℝ) (ha : a ≠ 0) :
    (∫ t in (γ - h)..γ, Real.sin ((t + h) * a) - Real.sin (t * a)) =
      2 * (1 - Real.cos (h * a)) * Real.cos (γ * a) / a := by
  have hi (l r : ℝ) :
      (∫ t in l..r, Real.sin (t * a)) =
        (Real.cos (l * a) - Real.cos (r * a)) / a := by
    apply (eq_div_iff ha).2
    rw [mul_comm, intervalIntegral.mul_integral_comp_mul_right, integral_sin]
  have hshift :
      (∫ t in (γ - h)..γ, Real.sin ((t + h) * a)) =
        ∫ t in γ..(γ + h), Real.sin (t * a) := by
    simpa only [sub_add_cancel] using
      (intervalIntegral.integral_comp_add_right (a := γ - h) (b := γ)
        (fun t : ℝ => Real.sin (t * a)) h)
  have hs : Continuous (fun t : ℝ => Real.sin ((t + h) * a)) := by fun_prop
  have ht : Continuous (fun t : ℝ => Real.sin (t * a)) := by fun_prop
  rw [intervalIntegral.integral_sub (hs.intervalIntegrable _ _) (ht.intervalIntegrable _ _),
    hshift, hi, hi, add_mul, sub_mul, Real.cos_add, Real.cos_sub]
  ring

/-- The same formula for a finite dictionary with arbitrary real weights. -/
theorem ordinate_weighted_sine_increment_integral {ι : Type*} (s : Finset ι)
    (w a : ι → ℝ) (γ h : ℝ) (ha : ∀ i ∈ s, a i ≠ 0) :
    (∫ t in (γ - h)..γ, ∑ i ∈ s,
      w i * (Real.sin ((t + h) * a i) - Real.sin (t * a i))) =
      ∑ i ∈ s, w i * (2 * (1 - Real.cos (h * a i)) * Real.cos (γ * a i) / a i) := by
  have hc (i : ι) : Continuous (fun t : ℝ =>
      w i * (Real.sin ((t + h) * a i) - Real.sin (t * a i))) := by fun_prop
  rw [intervalIntegral.integral_finsetSum (fun i _ => (hc i).intervalIntegrable _ _)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_const_mul, ordinate_sine_increment_integral γ h (a i) (ha i hi)]

end RiemannResearch.Analysis.MontgomeryOrdinateSineTrace
