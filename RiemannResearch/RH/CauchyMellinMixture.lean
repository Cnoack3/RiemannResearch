import RiemannResearch.RH.CompactFrequencyMellinRigidity
import RiemannResearch.RH.CauchyFourierTransform
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Cauchy mixtures of critical-line Mellin modes

For positive Cauchy scale `δ`, a continuous mixture of the critical-line
coordinates is exactly the Mellin mode at real part `1/2 + δ`. Every integral
here takes values in `ℂ` and is proved integrable coordinate by coordinate.
No integral of Hilbert-space-valued critical modes is asserted.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace RiemannResearch.RH.Pareto.SpectralObstruction

def cauchyMellinPoint (δ : ℝ≥0) (γ : ℝ) : ℂ :=
  verticalPoint (1 / 2 + (δ : ℝ)) γ

def cauchyMellinMixture (δ : ℝ≥0) (γ : ℝ) : ℕ → ℂ :=
  continuumMixture (1 / 2) (cauchyMeasure γ δ) (fun _ => 1)

@[simp] theorem cauchyMellinPoint_re (δ : ℝ≥0) (γ : ℝ) :
    (cauchyMellinPoint δ γ).re = 1 / 2 + (δ : ℝ) := by
  simp [cauchyMellinPoint]

private theorem real_cpow_vertical_factor (x σ : ℝ) (hx : 0 < x) (t : ℝ) :
    (x : ℂ) ^ (-verticalPoint σ t) =
      Complex.exp (-(σ : ℂ) * (Real.log x : ℂ)) *
        Complex.exp (-(t : ℂ) * Complex.I * (Real.log x : ℂ)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le,
    ← Complex.exp_add]
  congr 1
  unfold verticalPoint
  ring

private theorem finiteMeasure_integrable_fourierKernel
    (μ : Measure ℝ) [IsFiniteMeasure μ] (y : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (-(t : ℂ) * Complex.I * (y : ℂ))) μ := by
  apply (integrable_const (μ := μ) (1 : ℝ)).mono'
    (show AEStronglyMeasurable (fun t : ℝ =>
      Complex.exp (-(t : ℂ) * Complex.I * (y : ℂ))) μ from
      (by fun_prop : Continuous (fun t : ℝ =>
        Complex.exp (-(t : ℂ) * Complex.I * (y : ℂ)))).aestronglyMeasurable)
  filter_upwards [] with t
  simp [Complex.norm_exp]

private theorem finiteMeasure_integrable_vertical_cpow
    (μ : Measure ℝ) [IsFiniteMeasure μ] (x σ : ℝ) (hx : 0 < x) :
    Integrable (fun t : ℝ => (x : ℂ) ^ (-verticalPoint σ t)) μ := by
  simpa only [real_cpow_vertical_factor x σ hx] using
    (finiteMeasure_integrable_fourierKernel μ (Real.log x)).const_mul
      (Complex.exp (-(σ : ℂ) * (Real.log x : ℂ)))

/-- Each coordinate of a vertical-line mode is integrable against every
finite frequency measure; no frequency moment assumption is needed. -/
theorem finiteMeasure_integrable_mellinMode
    (μ : Measure ℝ) [IsFiniteMeasure μ] (σ : ℝ) (n : ℕ) :
    Integrable (fun t : ℝ => mellinMode (verticalPoint σ t) n) μ := by
  have h₁ : Integrable (fun t : ℝ =>
      ((n : ℂ) + 1) ^ (-verticalPoint σ t)) μ := by
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one] using
      finiteMeasure_integrable_vertical_cpow μ ((n : ℝ) + 1) σ (by positivity)
  have h₂ : Integrable (fun t : ℝ =>
      ((n : ℂ) + 2) ^ (-verticalPoint σ t)) μ := by
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_ofNat] using
      finiteMeasure_integrable_vertical_cpow μ ((n : ℝ) + 2) σ (by positivity)
  simpa only [mellinMode, Pi.sub_apply] using
    (h₁.sub h₂).const_mul (((n : ℂ) + 1) * ((n : ℂ) + 2))

/-- The Cauchy average of a Mellin power moves its real part to the right.
The hypothesis `1 ≤ x` selects the nonnegative logarithmic half-axis. -/
theorem cauchyMeasure_integral_vertical_cpow
    (γ : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0) (σ x : ℝ) (hx : 1 ≤ x) :
    (∫ t : ℝ, (x : ℂ) ^ (-verticalPoint σ t) ∂cauchyMeasure γ δ) =
      (x : ℂ) ^ (-verticalPoint (σ + (δ : ℝ)) γ) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hxpos
  simp_rw [real_cpow_vertical_factor x σ hxpos]
  rw [integral_const_mul, cauchyMeasure_integral_exp_neg_mul γ δ hδ,
    abs_of_nonneg (Real.log_nonneg hx), ← Complex.exp_add,
    Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hxpos.le]
  congr 1
  simp only [verticalPoint, Complex.ofReal_add]
  ring

/-- The coordinate integral exists absolutely, including at Cauchy scale zero. -/
theorem integrable_cauchyMellin_coordinate (δ : ℝ≥0) (γ : ℝ) (n : ℕ) :
    Integrable (fun t : ℝ => mellinMode (MellinFrequency.criticalPoint t) n)
      (cauchyMeasure γ δ) := by
  simpa only [verticalPoint_half] using
    finiteMeasure_integrable_mellinMode (cauchyMeasure γ δ) (1 / 2) n

/-- Positive Cauchy averaging gives the actual off-line Mellin mode. -/
theorem cauchyMeasure_integral_mellinMode
    (γ : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0) (σ : ℝ) (n : ℕ) :
    (∫ t : ℝ, mellinMode (verticalPoint σ t) n ∂cauchyMeasure γ δ) =
      mellinMode (verticalPoint (σ + (δ : ℝ)) γ) n := by
  have hi₁ : Integrable (fun t : ℝ =>
      ((n : ℂ) + 1) ^ (-verticalPoint σ t)) (cauchyMeasure γ δ) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one] using
      finiteMeasure_integrable_vertical_cpow (cauchyMeasure γ δ)
        ((n : ℝ) + 1) σ (by positivity)
  have hi₂ : Integrable (fun t : ℝ =>
      ((n : ℂ) + 2) ^ (-verticalPoint σ t)) (cauchyMeasure γ δ) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_ofNat] using
      finiteMeasure_integrable_vertical_cpow (cauchyMeasure γ δ)
        ((n : ℝ) + 2) σ (by positivity)
  have h₁ := cauchyMeasure_integral_vertical_cpow γ δ hδ σ
    ((n : ℝ) + 1) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have h₂ := cauchyMeasure_integral_vertical_cpow γ δ hδ σ
    ((n : ℝ) + 2) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  simp only [Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one, Complex.ofReal_ofNat] at h₁ h₂
  simp only [mellinMode]
  rw [integral_const_mul, integral_sub hi₁ hi₂, h₁, h₂]

/-- Equality of the actual coordinate sequences, without any claim that the
individual critical modes are Hilbert-space-valued. -/
theorem cauchyMellinMixture_eq_mellinMode
    (δ : ℝ≥0) (γ : ℝ) (hδ : δ ≠ 0) :
    cauchyMellinMixture δ γ = mellinMode (cauchyMellinPoint δ γ) := by
  funext n
  simpa only [cauchyMellinMixture, continuumMixture, one_mul,
    cauchyMellinPoint] using
    cauchyMeasure_integral_mellinMode γ δ hδ (1 / 2) n

/-- The same coordinate integral written with the ordinary positive Cauchy
density and Lebesgue measure. -/
theorem integral_cauchyPDFReal_mul_criticalMode
    (δ : ℝ≥0) (γ : ℝ) (hδ : δ ≠ 0) (n : ℕ) :
    (∫ t : ℝ, (cauchyPDFReal γ δ t : ℂ) *
      mellinMode (MellinFrequency.criticalPoint t) n) =
        mellinMode (cauchyMellinPoint δ γ) n := by
  have h := cauchyMeasure_integral_mellinMode γ δ hδ (1 / 2) n
  rw [cauchyMeasure_of_scale_ne_zero γ hδ,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_cauchyPDF γ δ)
      (ae_of_all _ fun t => by simp [cauchyPDF])] at h
  simpa only [cauchyPDF, ENNReal.toReal_ofReal (cauchyPDF_pos γ hδ _).le,
    Complex.real_smul, verticalPoint_half, cauchyMellinPoint] using h

/-- Absolute Lebesgue integrability of the displayed density mixture. -/
theorem integrable_cauchyPDFReal_mul_criticalMode
    (δ : ℝ≥0) (γ : ℝ) (hδ : δ ≠ 0) (n : ℕ) :
    Integrable (fun t : ℝ => (cauchyPDFReal γ δ t : ℂ) *
      mellinMode (MellinFrequency.criticalPoint t) n) := by
  have h := integrable_cauchyMellin_coordinate δ γ n
  rw [cauchyMeasure_of_scale_ne_zero γ hδ,
    integrable_withDensity_iff_integrable_smul'
      (measurable_cauchyPDF γ δ)
      (ae_of_all _ fun t => by simp [cauchyPDF])] at h
  simpa only [cauchyPDF, ENNReal.toReal_ofReal (cauchyPDF_pos γ hδ _).le,
    Complex.real_smul] using h

end RiemannResearch.RH.Pareto.SpectralObstruction
