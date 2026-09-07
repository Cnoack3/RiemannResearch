import RiemannResearch.Analysis.BilateralLaplaceDifferential

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Vertical-strip decay of the actual bilateral Laplace integral

The estimates use the real part of the parameter, rather than its norm.
The second-derivative identity supplies uniform quadratic vertical decay,
without an assumed spectral decay or an omitted boundary term.
-/

open MeasureTheory

namespace MeasureTheory.BilateralLaplace

theorem kernel_norm_le_re (s : ℂ) (y : ℝ) :
    ‖kernel s y‖ ≤ Real.exp (|s.re| * |y|) := by
  rw [kernel, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (-s * (y : ℂ)).re = -s.re * y := by simp
    _ ≤ |-s.re * y| := le_abs_self _
    _ = |s.re| * |y| := by simp [abs_mul]

theorem norm_centeredTransform_le_weighted_integral (f : ℝ → ℂ) {s : ℂ} {a : ℝ}
    (hweight : Integrable (fun y : ℝ => Real.exp (a * |y|) * ‖f y‖))
    (hs : |(s - 1 / 2).re| ≤ a) :
    ‖centeredTransform f s‖ ≤
      ∫ y : ℝ, Real.exp (a * |y|) * ‖f y‖ := by
  unfold centeredTransform transform
  apply norm_integral_le_of_norm_le hweight
  apply ae_of_all
  intro y
  have hk : ‖kernel (s - 1 / 2) y‖ ≤ Real.exp (a * |y|) :=
    (kernel_norm_le_re (s - 1 / 2) y).trans <|
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs (abs_nonneg y))
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left hk (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem norm_centeredTransform_mul_parameter_sq_le {f : ℝ → ℂ}
    (hf : HasExponentialMoments f) (hf' : HasExponentialMoments (deriv f))
    (hf'' : HasExponentialMoments (deriv (deriv f)))
    (hd : Differentiable ℝ f) (hd' : Differentiable ℝ (deriv f))
    {s : ℂ} {a : ℝ}
    (hweight : Integrable (fun y : ℝ =>
      Real.exp (a * |y|) * ‖deriv (deriv f) y‖))
    (hs : |(s - 1 / 2).re| ≤ a) :
    ‖s - 1 / 2‖ ^ 2 * ‖centeredTransform f s‖ ≤
      ∫ y : ℝ, Real.exp (a * |y|) * ‖deriv (deriv f) y‖ := by
  calc
    ‖s - 1 / 2‖ ^ 2 * ‖centeredTransform f s‖ =
        ‖centeredTransform (deriv (deriv f)) s‖ := by
      rw [centeredTransform_second_deriv hf hf' hf'' hd hd' s, norm_mul, norm_pow]
    _ ≤ _ := norm_centeredTransform_le_weighted_integral _ hweight hs

/-- A global-in-height quadratic bound, with no division by an imaginary part. -/
theorem vertical_decay_two {f : ℝ → ℂ}
    (hf : HasExponentialMoments f) (hf' : HasExponentialMoments (deriv f))
    (hf'' : HasExponentialMoments (deriv (deriv f)))
    (hd : Differentiable ℝ f) (hd' : Differentiable ℝ (deriv f))
    {s : ℂ} {a : ℝ}
    (hweight : Integrable (fun y : ℝ => Real.exp (a * |y|) * ‖f y‖))
    (hweight'' : Integrable (fun y : ℝ =>
      Real.exp (a * |y|) * ‖deriv (deriv f) y‖))
    (hs : |(s - 1 / 2).re| ≤ a) :
    (1 + |s.im| ^ 2) * ‖centeredTransform f s‖ ≤
      (∫ y : ℝ, Real.exp (a * |y|) * ‖f y‖) +
        ∫ y : ℝ, Real.exp (a * |y|) * ‖deriv (deriv f) y‖ := by
  have him : |s.im| ≤ ‖s - 1 / 2‖ := by
    simpa using Complex.abs_im_le_norm (s - 1 / 2)
  have hsq := pow_le_pow_left₀ (abs_nonneg s.im) him 2
  have hmul := mul_le_mul_of_nonneg_right hsq (norm_nonneg (centeredTransform f s))
  have h₀ := norm_centeredTransform_le_weighted_integral f hweight hs
  have h₂ := norm_centeredTransform_mul_parameter_sq_le hf hf' hf'' hd hd' hweight'' hs
  nlinarith

end MeasureTheory.BilateralLaplace

namespace RiemannResearch.Analysis

theorem SuperexponentialDecay.vertical_decay_two {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hf' : SuperexponentialDecay (deriv f))
    (hf'' : SuperexponentialDecay (deriv (deriv f)))
    (hd : Differentiable ℝ f) (hd' : Differentiable ℝ (deriv f))
    (hc'' : Continuous (deriv (deriv f)))
    {s : ℂ} {a : ℝ} (ha : 0 ≤ a) (hs : |(s - 1 / 2).re| ≤ a) :
    (1 + |s.im| ^ 2) * ‖BilateralLaplace.centeredTransform f s‖ ≤
      (∫ y : ℝ, Real.exp (a * |y|) * ‖f y‖) +
        ∫ y : ℝ, Real.exp (a * |y|) * ‖deriv (deriv f) y‖ :=
  BilateralLaplace.vertical_decay_two
    (hf.hasExponentialMoments hd.continuous)
    (hf'.hasExponentialMoments hd'.continuous)
    (hf''.hasExponentialMoments hc'') hd hd'
    (hf.integrable_weighted_norm hd.continuous ha)
    (hf''.integrable_weighted_norm hc'' ha) hs

end RiemannResearch.Analysis
