import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Fourier transform of a Cauchy probability measure

The characteristic function is proved by Fourier inversion of an integrable
two-sided exponential. No transform identity is assumed.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set Complex
open scoped FourierTransform NNReal ENNReal

namespace RiemannResearch.RH.Pareto.SpectralObstruction

private def laplaceFourierIntegrand (a b x : ℝ) : ℂ :=
  Complex.exp (-(a : ℂ) * (|x| : ℝ) - Complex.I * (b : ℂ) * (x : ℂ))

private theorem laplaceFourierIntegrand_on_neg (a b x : ℝ) (hx : x ≤ 0) :
    laplaceFourierIntegrand a b x = Complex.exp (((a : ℂ) - Complex.I * b) * x) := by
  unfold laplaceFourierIntegrand
  rw [abs_of_nonpos hx, Complex.ofReal_neg]
  congr 1
  ring

private theorem laplaceFourierIntegrand_on_pos (a b x : ℝ) (hx : 0 ≤ x) :
    laplaceFourierIntegrand a b x = Complex.exp ((-(a : ℂ) - Complex.I * b) * x) := by
  unfold laplaceFourierIntegrand
  rw [abs_of_nonneg hx]
  congr 1
  ring

private theorem laplaceFourierIntegrand_integrable (a b : ℝ) (ha : 0 < a) :
    Integrable (laplaceFourierIntegrand a b) := by
  have hneg : IntegrableOn (laplaceFourierIntegrand a b) (Iic 0) := by
    apply (integrableOn_exp_mul_complex_Iic (a := (a : ℂ) - I * b)
      (by simpa using ha) 0).congr_fun _ measurableSet_Iic
    intro x hx
    exact (laplaceFourierIntegrand_on_neg a b x hx).symm
  have hpos : IntegrableOn (laplaceFourierIntegrand a b) (Ioi 0) := by
    apply (integrableOn_exp_mul_complex_Ioi (a := -(a : ℂ) - I * b)
      (by simpa using neg_neg_of_pos ha) 0).congr_fun _ measurableSet_Ioi
    intro x hx
    exact (laplaceFourierIntegrand_on_pos a b x hx.le).symm
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact integrableOn_union.mpr ⟨hneg, hpos⟩

private theorem integral_laplaceFourierIntegrand (a b : ℝ) (ha : 0 < a) :
    (∫ x : ℝ, laplaceFourierIntegrand a b x) =
      ((2 * a / (a ^ 2 + b ^ 2) : ℝ) : ℂ) := by
  have hi := laplaceFourierIntegrand_integrable a b ha
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) hi.integrableOn hi.integrableOn]
  have hn : (∫ x : ℝ in Iic 0, laplaceFourierIntegrand a b x) =
      1 / ((a : ℂ) - I * b) := by
    rw [setIntegral_congr_fun measurableSet_Iic
      (fun x hx => laplaceFourierIntegrand_on_neg a b x hx)]
    simpa using integral_exp_mul_complex_Iic (a := (a : ℂ) - I * b)
      (by simpa using ha) 0
  have hp : (∫ x : ℝ in Ioi 0, laplaceFourierIntegrand a b x) =
      -(1 : ℂ) / (-(a : ℂ) - I * b) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun x hx => laplaceFourierIntegrand_on_pos a b x hx.le)]
    simpa using integral_exp_mul_complex_Ioi (a := -(a : ℂ) - I * b)
      (by simpa using neg_neg_of_pos ha) 0
  rw [hn, hp]
  have h1 : (a : ℂ) - I * b ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 : -(a : ℂ) - I * b ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hab : a ^ 2 + b ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have habc : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hab
  push_cast
  field_simp [habc]
  ring_nf
  simp [I_sq]

private def laplaceKernel (δ : ℝ≥0) (x : ℝ) : ℂ :=
  Complex.exp (-((2 * Real.pi * (δ : ℝ) * |x| : ℝ) : ℂ))

private theorem laplaceKernel_integrable (δ : ℝ≥0) (hδ : δ ≠ 0) :
    Integrable (laplaceKernel δ) := by
  have hd : (0 : ℝ) < δ := by exact_mod_cast (pos_iff_ne_zero.mpr hδ)
  have heq : laplaceKernel δ = laplaceFourierIntegrand (2 * Real.pi * δ) 0 := by
    funext x
    simp [laplaceKernel, laplaceFourierIntegrand, Complex.ofReal_mul, neg_mul]
  rw [heq]
  exact laplaceFourierIntegrand_integrable (2 * Real.pi * δ) 0 (by positivity)

private theorem fourier_laplaceKernel (δ : ℝ≥0) (hδ : δ ≠ 0) (t : ℝ) :
    𝓕 (laplaceKernel δ) t = (ProbabilityTheory.cauchyPDFReal 0 δ t : ℂ) := by
  have hd : (0 : ℝ) < δ := by exact_mod_cast (pos_iff_ne_zero.mpr hδ)
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, laplaceKernel, ← Complex.exp_add]
  have heq : (fun x : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * x * t) : ℂ) * I +
        -((2 * Real.pi * (δ : ℝ) * |x| : ℝ) : ℂ))) =
      laplaceFourierIntegrand (2 * Real.pi * δ) (2 * Real.pi * t) := by
    funext x
    unfold laplaceFourierIntegrand
    congr 1
    push_cast
    ring
  rw [heq, integral_laplaceFourierIntegrand _ _ (by positivity)]
  congr 1
  unfold ProbabilityTheory.cauchyPDFReal
  simp only [sub_zero]
  field_simp
  <;> ring

private theorem fourier_cauchyPDF_zero (δ : ℝ≥0) (hδ : δ ≠ 0) (t : ℝ) :
    𝓕 (fun x : ℝ => (ProbabilityTheory.cauchyPDFReal 0 δ x : ℂ)) t =
      laplaceKernel δ t := by
  have hf := laplaceKernel_integrable δ hδ
  have heq : 𝓕 (laplaceKernel δ) =
      fun x : ℝ => (ProbabilityTheory.cauchyPDFReal 0 δ x : ℂ) := by
    funext x
    exact fourier_laplaceKernel δ hδ x
  have hft : Integrable (𝓕 (laplaceKernel δ)) := by
    rw [heq]
    exact (ProbabilityTheory.integrable_cauchyPDFReal (x₀ := 0) (γ := δ)).ofReal
  have hinv := hf.fourierInv_fourier_eq hft (v := -t)
    (show ContinuousAt (laplaceKernel δ) (-t) by unfold laplaceKernel; fun_prop)
  rw [Real.fourierInv_eq_fourier_neg, heq, neg_neg] at hinv
  simpa [laplaceKernel, abs_neg] using hinv

/-- The Cauchy probability measure has characteristic function
`exp (-δ |y| - i γ y)`, with the negative Fourier convention. -/
theorem cauchyMeasure_integral_exp_neg_mul (γ : ℝ) (δ : ℝ≥0)
    (hδ : δ ≠ 0) (y : ℝ) :
    (∫ t : ℝ, Complex.exp (-(t : ℂ) * I * (y : ℂ))
      ∂ProbabilityTheory.cauchyMeasure γ δ) =
      Complex.exp (-((δ : ℝ) : ℂ) * (|y| : ℝ) - (γ : ℂ) * I * (y : ℂ)) := by
  have hpdf : ∀ t : ℝ, (ProbabilityTheory.cauchyPDF γ δ t).toReal =
      ProbabilityTheory.cauchyPDFReal γ δ t := by
    intro t
    exact ENNReal.toReal_ofReal (ProbabilityTheory.cauchyPDF_pos γ hδ t).le
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero γ hδ,
    integral_withDensity_eq_integral_toReal_smul
      (ProbabilityTheory.measurable_cauchyPDF γ δ)
      (Filter.Eventually.of_forall (fun t => ENNReal.ofReal_lt_top))]
  simp_rw [hpdf, Complex.real_smul]
  rw [← integral_add_right_eq_self
    (fun t : ℝ => (ProbabilityTheory.cauchyPDFReal γ δ t : ℂ) *
      Complex.exp (-(t : ℂ) * I * (y : ℂ))) γ]
  have hshift : (fun t : ℝ => (ProbabilityTheory.cauchyPDFReal γ δ (t + γ) : ℂ) *
      Complex.exp (-((t + γ : ℝ) : ℂ) * I * (y : ℂ))) =
      fun t : ℝ => Complex.exp (-(γ : ℂ) * I * (y : ℂ)) *
        (Complex.exp (-(t : ℂ) * I * (y : ℂ)) *
          (ProbabilityTheory.cauchyPDFReal 0 δ t : ℂ)) := by
    funext t
    have hden : ProbabilityTheory.cauchyPDFReal γ δ (t + γ) =
        ProbabilityTheory.cauchyPDFReal 0 δ t := by
      simp [ProbabilityTheory.cauchyPDFReal]
    rw [hden, Complex.ofReal_add]
    have he : -((t : ℂ) + γ) * I * y = -(γ : ℂ) * I * y + -(t : ℂ) * I * y := by ring
    rw [he, Complex.exp_add]
    ring
  rw [hshift, integral_const_mul]
  have hfreq : (∫ t : ℝ, Complex.exp (-(t : ℂ) * I * (y : ℂ)) *
      (ProbabilityTheory.cauchyPDFReal 0 δ t : ℂ)) = laplaceKernel δ (y / (2 * Real.pi)) := by
    rw [← fourier_cauchyPDF_zero δ hδ, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [smul_eq_mul]
    congr 2
    push_cast
    field_simp
    <;> ring
  rw [hfreq, laplaceKernel, ← Complex.exp_add]
  congr 1
  have hp : 0 < 2 * Real.pi := by positivity
  rw [abs_div, abs_of_pos hp]
  push_cast
  field_simp
  <;> ring

end RiemannResearch.RH.Pareto.SpectralObstruction
