import RiemannResearch.Analysis.BilateralLaplaceEntire
import RiemannResearch.Analysis.SuperexponentialSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Push

/-! Source: RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md, section 3.6.
Genuine full-real Plancherel in the centered Laplace convention.
No spectral norm identity or Plancherel premise is assumed.
The mixed arithmetic completion factorization remains a separate obligation.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace MeasureTheory.BilateralLaplace

/-- Mathlib's frequency has the `2π` convention. -/
theorem centeredTransform_critical_fourier (f : ℝ → ℂ) (ξ : ℝ) :
    centeredTransform f ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) =
      𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold centeredTransform transform kernel
  apply integral_congr_ae
  filter_upwards [] with y
  rw [smul_eq_mul, mul_comm (f y)]
  congr 1
  congr 1
  push_cast
  ring

/-- The spectral energy density is genuinely integrable over the full line. -/
theorem integrable_centeredTransform_critical_sq (f : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ =>
      ‖centeredTransform f ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  apply (integrable_comp_mul_right_iff _ hp).mp
  have hi := (memLp_two_iff_integrable_sq_norm
    ((𝓕 f).memLp 2).aestronglyMeasurable).mp ((𝓕 f).memLp 2)
  simpa only [mul_comm _ (2 * Real.pi), ← mul_assoc,
    centeredTransform_critical_fourier, ← SchwartzMap.fourier_coe] using hi

/-- Full spectral energy, with the exact normalization from the chat. -/
theorem centeredTransform_plancherel (f : SchwartzMap ℝ ℂ) :
    (∫ y : ℝ, ‖f y‖ ^ 2) = (1 / (2 * Real.pi)) *
      ∫ t : ℝ, ‖centeredTransform f
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  have he : (∫ ξ : ℝ, ‖centeredTransform f
      ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)‖ ^ 2) =
      ∫ y : ℝ, ‖f y‖ ^ 2 := by
    simp_rw [centeredTransform_critical_fourier, ← SchwartzMap.fourier_coe]
    exact f.integral_norm_sq_fourier
  have hs := Measure.integral_comp_mul_right
    (fun t : ℝ => ‖centeredTransform f
      ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) (2 * Real.pi)
  have hp : 0 < (2 * Real.pi : ℝ) := by positivity
  apply he.symm.trans
  simpa only [mul_comm _ (2 * Real.pi), ← mul_assoc,
    abs_of_pos (inv_pos.mpr hp), smul_eq_mul, one_div] using hs

/-- Smooth superexponential functions satisfy the exact same Plancherel identity;
the Schwartz membership is supplied by the proved conversion, not assumed. -/
theorem centeredTransform_plancherel_of_smoothSuperexponential
    (f : ℝ → ℂ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hd : ∀ j, RiemannResearch.Analysis.SuperexponentialDecay (iteratedDeriv j f)) :
    (∫ y : ℝ, ‖f y‖ ^ 2) = (1 / (2 * Real.pi)) *
      ∫ t : ℝ, ‖centeredTransform f
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  exact centeredTransform_plancherel
    (RiemannResearch.Analysis.schwartzMapOfSmoothSuperexponential f hf hd)

end MeasureTheory.BilateralLaplace
