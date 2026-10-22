import RiemannResearch.Analysis.SmoothCompactCutoff
import RiemannResearch.Analysis.SmoothSuperexponentialDecay
import RiemannResearch.Analysis.BilateralLaplaceDecay
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Weighted L1 convergence of actual compact smooth cutoffs

Every derivative converges in each exponential weighted L1 norm. The majorant
comes from the exact finite Leibniz formula, so the derivative corrections
introduced by the cutoff are included.
-/

open scoped Topology BigOperators
open Filter MeasureTheory

namespace RiemannResearch.Analysis

private theorem contDiff_iteratedDeriv_smooth {f : ℝ → ℂ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (j : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv j f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv j hf

/-- Integrability of the actual radius-independent Leibniz majorant. -/
theorem integrable_weighted_cutoffDerivativeMajorant {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    Integrable (fun x : ℝ => Real.exp (a * |x|) * cutoffDerivativeMajorant f j x) := by
  have hi (i : ℕ) : Integrable (fun x : ℝ =>
      (j.choose i : ℝ) * cutoffDerivativeBound i *
        (Real.exp (a * |x|) * ‖iteratedDeriv (j-i) f x‖)) :=
    ((hf.2 (j-i)).integrable_weighted_norm
      (contDiff_iteratedDeriv_smooth hf.1 (j-i)).continuous ha).const_mul _
  convert integrable_finsetSum (Finset.range (j+1)) (fun i _ => hi i) using 1 <;>
    first | rfl | skip
  ext x
  simp only [cutoffDerivativeMajorant, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Every derivative of every cutoff has its required weighted L1 norm. -/
theorem integrable_weighted_iteratedDeriv_compactCutoff {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) {a : ℝ} (ha : 0 ≤ a) (N j : ℕ) :
    Integrable (fun x : ℝ =>
      Real.exp (a * |x|) * ‖iteratedDeriv j (compactCutoff N f) x‖) := by
  apply (integrable_weighted_cutoffDerivativeMajorant hf ha j).mono'
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
      (contDiff_iteratedDeriv_smooth (compactCutoff_contDiff hf.1 N) j).continuous.norm).aestronglyMeasurable
  · apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_iteratedDeriv_compactCutoff_le hf.1 N j x)
      (Real.exp_nonneg _)

/-- Uniform weighted norm control includes all cutoff-derivative terms. -/
theorem weighted_iteratedDeriv_compactCutoff_integral_le {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) {a : ℝ} (ha : 0 ≤ a) (N j : ℕ) :
    (∫ x : ℝ, Real.exp (a * |x|) * ‖iteratedDeriv j (compactCutoff N f) x‖) ≤
      ∫ x : ℝ, Real.exp (a * |x|) * cutoffDerivativeMajorant f j x := by
  apply integral_mono (integrable_weighted_iteratedDeriv_compactCutoff hf ha N j)
    (integrable_weighted_cutoffDerivativeMajorant hf ha j)
  intro x
  exact mul_le_mul_of_nonneg_left (norm_iteratedDeriv_compactCutoff_le hf.1 N j x)
    (Real.exp_nonneg _)

/-- Actual exponentially weighted L1 convergence, at every derivative order. -/
theorem tendsto_weighted_iteratedDeriv_compactCutoff_sub {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    Tendsto (fun N : ℕ => ∫ x : ℝ, Real.exp (a * |x|) *
      ‖iteratedDeriv j (compactCutoff N f) x - iteratedDeriv j f x‖) atTop (𝓝 0) := by
  let B : ℝ → ℝ := fun x => Real.exp (a * |x|) *
    (cutoffDerivativeMajorant f j x + ‖iteratedDeriv j f x‖)
  have hB : Integrable B := by
    convert (integrable_weighted_cutoffDerivativeMajorant hf ha j).add
      ((hf.2 j).integrable_weighted_norm (contDiff_iteratedDeriv_smooth hf.1 j).continuous ha)
        using 1 <;> first | rfl | skip
    ext x
    simp only [B, Pi.add_apply, mul_add]
  have hzero : (∫ _ : ℝ, (0 : ℝ)) = 0 := by simp
  rw [← hzero]
  refine tendsto_integral_of_dominated_convergence B
    (f := fun _ : ℝ => (0 : ℝ)) ?_ hB ?_ ?_
  · intro N
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
      (((contDiff_iteratedDeriv_smooth (compactCutoff_contDiff hf.1 N) j).continuous).sub
        (contDiff_iteratedDeriv_smooth hf.1 j).continuous).norm).aestronglyMeasurable
  · intro N
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact (norm_sub_le _ _).trans
      (add_le_add (norm_iteratedDeriv_compactCutoff_le hf.1 N j x) le_rfl)
  · apply ae_of_all
    intro x
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
    filter_upwards [eventually_iteratedDeriv_compactCutoff_eq f j x] with N hN
    simp [hN]

/-- Pointwise convergence of the actual centered Laplace integrals. -/
theorem tendsto_centeredTransform_compactCutoff {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (s : ℂ) :
    Tendsto (fun N : ℕ => BilateralLaplace.centeredTransform (compactCutoff N f) s)
      atTop (𝓝 (BilateralLaplace.centeredTransform f s)) := by
  have hk : Continuous (BilateralLaplace.kernel (s-1/2)) := by
    unfold BilateralLaplace.kernel
    fun_prop
  unfold BilateralLaplace.centeredTransform BilateralLaplace.transform
  apply tendsto_integral_of_dominated_convergence
    (fun x : ℝ => Real.exp (|(s - 1/2).re| * |x|) * ‖f x‖)
  · intro N
    exact ((compactCutoff_contDiff hf.1 N).continuous.mul
      hk).aestronglyMeasurable
  · exact hf.decay.integrable_weighted_norm hf.1.continuous (abs_nonneg _)
  · intro N
    apply ae_of_all
    intro x
    rw [compactCutoff, Pi.mul_apply, norm_mul, norm_mul]
    have h1 := norm_smoothCutoff_le_one N x
    have h2 := BilateralLaplace.kernel_norm_le_re (s-1/2) x
    calc
      ‖smoothCutoff N x‖ * ‖f x‖ * ‖BilateralLaplace.kernel (s-1/2) x‖ ≤
        1 * ‖f x‖ * Real.exp (|(s-1/2).re| * |x|) := by gcongr
      _ = _ := by ring
  · apply ae_of_all
    intro x
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
      f x * BilateralLaplace.kernel (s-1/2) x) atTop
        (𝓝 (f x * BilateralLaplace.kernel (s-1/2) x))).congr'
    filter_upwards [eventually_iteratedDeriv_compactCutoff_eq f 0 x] with N hN
    simpa only [iteratedDeriv_zero] using congrArg (fun z =>
      z * BilateralLaplace.kernel (s-1/2) x) hN.symm

end RiemannResearch.Analysis
