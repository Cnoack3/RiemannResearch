import RiemannResearch.Analysis.CompactCutoffConvergence

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Uniform vertical decay of actual compact-cutoff transforms

The bound is independent of the cutoff radius. Its two constants are actual
weighted integrals of the complete finite Leibniz majorants, so every cutoff
derivative term is included. No uniform transform bound is assumed.
-/

open MeasureTheory

namespace RiemannResearch.Analysis

noncomputable def cutoffVerticalBound (f : ℝ → ℂ) (a : ℝ) : ℝ :=
  (∫ x : ℝ, Real.exp (a * |x|) * cutoffDerivativeMajorant f 0 x) +
    ∫ x : ℝ, Real.exp (a * |x|) * cutoffDerivativeMajorant f 2 x

theorem cutoffVerticalBound_nonneg (f : ℝ → ℂ) (a : ℝ) :
    0 ≤ cutoffVerticalBound f a := by
  unfold cutoffVerticalBound
  exact add_nonneg
    (integral_nonneg (fun x => mul_nonneg (Real.exp_nonneg _)
      (cutoffDerivativeMajorant_nonneg f 0 x)))
    (integral_nonneg (fun x => mul_nonneg (Real.exp_nonneg _)
      (cutoffDerivativeMajorant_nonneg f 2 x)))

theorem hasExponentialMoments_iteratedDeriv_compactCutoff {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (N j : ℕ) :
    BilateralLaplace.HasExponentialMoments (iteratedDeriv j (compactCutoff N f)) := by
  have hc : Continuous (iteratedDeriv j (compactCutoff N f)) := by
    rw [iteratedDeriv_eq_iterate]
    exact (ContDiff.iterate_deriv j (compactCutoff_contDiff hf.1 N)).continuous
  apply BilateralLaplace.hasExponentialMoments_of_weighted_integrable hc.aestronglyMeasurable
  intro a ha
  exact integrable_weighted_iteratedDeriv_compactCutoff hf ha.le N j

theorem vertical_decay_two_compactCutoff {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) {a : ℝ} (ha : 0 ≤ a)
    (N : ℕ) (s : ℂ) (hs : |(s - 1 / 2).re| ≤ a) :
    (1 + |s.im| ^ 2) * ‖BilateralLaplace.centeredTransform (compactCutoff N f) s‖ ≤
      cutoffVerticalBound f a := by
  have hc := compactCutoff_contDiff hf.1 N
  have hc' : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv (compactCutoff N f)) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      ContDiff.iterate_deriv 1 hc
  have hm₀ : BilateralLaplace.HasExponentialMoments (compactCutoff N f) := by
    simpa only [iteratedDeriv_zero] using
      hasExponentialMoments_iteratedDeriv_compactCutoff hf N 0
  have hm₁ : BilateralLaplace.HasExponentialMoments (deriv (compactCutoff N f)) := by
    simpa only [iteratedDeriv_eq_iterate, Function.iterate_succ_apply,
      Function.iterate_zero_apply] using
      hasExponentialMoments_iteratedDeriv_compactCutoff hf N 1
  have hm₂ : BilateralLaplace.HasExponentialMoments (deriv (deriv (compactCutoff N f))) := by
    simpa only [iteratedDeriv_eq_iterate, Function.iterate_succ_apply,
      Function.iterate_zero_apply] using
      hasExponentialMoments_iteratedDeriv_compactCutoff hf N 2
  have hi₀ : Integrable (fun x : ℝ => Real.exp (a * |x|) * ‖compactCutoff N f x‖) := by
    simpa only [iteratedDeriv_zero] using
      integrable_weighted_iteratedDeriv_compactCutoff hf ha N 0
  have hi₂ : Integrable (fun x : ℝ =>
      Real.exp (a * |x|) * ‖deriv (deriv (compactCutoff N f)) x‖) := by
    simpa only [iteratedDeriv_eq_iterate, Function.iterate_succ_apply,
      Function.iterate_zero_apply] using
      integrable_weighted_iteratedDeriv_compactCutoff hf ha N 2
  have h₀ : (∫ x : ℝ, Real.exp (a * |x|) * ‖compactCutoff N f x‖) ≤
      ∫ x : ℝ, Real.exp (a * |x|) * cutoffDerivativeMajorant f 0 x := by
    simpa only [iteratedDeriv_zero] using
      weighted_iteratedDeriv_compactCutoff_integral_le hf ha N 0
  have h₂ : (∫ x : ℝ, Real.exp (a * |x|) *
      ‖deriv (deriv (compactCutoff N f)) x‖) ≤
      ∫ x : ℝ, Real.exp (a * |x|) * cutoffDerivativeMajorant f 2 x := by
    simpa only [iteratedDeriv_eq_iterate, Function.iterate_succ_apply,
      Function.iterate_zero_apply] using
      weighted_iteratedDeriv_compactCutoff_integral_le hf ha N 2
  exact (BilateralLaplace.vertical_decay_two hm₀ hm₁ hm₂
    (hc.differentiable (by simp)) (hc'.differentiable (by simp)) hi₀ hi₂ hs).trans
    (add_le_add h₀ h₂)

theorem norm_centeredTransform_compactCutoff_le {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) {a : ℝ} (ha : 0 ≤ a)
    (N : ℕ) (s : ℂ) (hs : |(s - 1 / 2).re| ≤ a) :
    ‖BilateralLaplace.centeredTransform (compactCutoff N f) s‖ ≤
      cutoffVerticalBound f a / (1 + |s.im| ^ 2) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + |s.im| ^ 2)).2
  simpa only [mul_comm] using vertical_decay_two_compactCutoff hf ha N s hs

end RiemannResearch.Analysis
