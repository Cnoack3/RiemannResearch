import RiemannResearch.Analysis.ScaledKernelApproximation
import Mathlib.Analysis.Calculus.ParametricIntegral

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual differentiation of the scaled kernel integral

The parameter derivative is justified by dominated differentiation. Its
integrable majorant is the absolute kernel times a uniform derivative bound.
No identity for the differentiated convolution is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RiemannResearch.Analysis

theorem hasDerivAt_scaledKernelConvolution (h f : ℝ → ℝ)
    (hh : Integrable h) (hfd : Differentiable ℝ f)
    (hdfc : Continuous (deriv f)) (M0 M1 : ℝ)
    (hM0 : ∀ x, |f x| ≤ M0) (hM1 : ∀ x, |deriv f x| ≤ M1)
    (R x : ℝ) :
    HasDerivAt (scaledKernelConvolution h f R)
      (scaledKernelConvolution h (deriv f) R x) x := by
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun v : ℝ => h v * f (t - v / R)) volume := by
    have hc : Continuous (fun v : ℝ => f (t - v / R)) := by
      have hfc := hfd.continuous
      fun_prop
    exact hh.aestronglyMeasurable.mul hc.aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable
      (fun v : ℝ => h v * deriv f (x - v / R)) volume := by
    have hc : Continuous (fun v : ℝ => deriv f (x - v / R)) := by fun_prop
    exact hh.aestronglyMeasurable.mul hc.aestronglyMeasurable
  have hb : ∀ᵐ v : ℝ, ∀ t ∈ (univ : Set ℝ),
      ‖h v * deriv f (t - v / R)‖ ≤ |h v| * M1 := by
    apply ae_of_all
    intro v t _
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM1 _) (abs_nonneg _)
  have hd : ∀ᵐ v : ℝ, ∀ t ∈ (univ : Set ℝ),
      HasDerivAt (fun z : ℝ => h v * f (z - v / R))
        (h v * deriv f (t - v / R)) t := by
    apply ae_of_all
    intro v t _
    have hin : HasDerivAt (fun z : ℝ => z - v / R) (1 : ℝ) t := by
      convert (hasDerivAt_id t).sub_const (v / R) using 1 <;> rfl
    have hs : HasDerivAt (fun z : ℝ => f (z - v / R))
        (deriv f (t - v / R)) t := by
      convert (hfd (t - v / R)).hasDerivAt.comp t hin using 1 <;>
        first | rfl | simp
    exact hs.const_mul (h v)
  have hresult := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t v : ℝ => h v * f (t - v / R))
    (F' := fun t v : ℝ => h v * deriv f (t - v / R))
    (bound := fun v : ℝ => |h v| * M1) (s := univ) (x₀ := x)
    Filter.univ_mem (Filter.Eventually.of_forall hmeas)
    (integrable_scaledKernel_integrand h f hh hfd.continuous M0 hM0 R x)
    hdmeas hb (hh.abs.mul_const M1) hd).2
  convert hresult using 1 <;> rfl

theorem deriv_scaledKernelConvolution (h f : ℝ → ℝ)
    (hh : Integrable h) (hfd : Differentiable ℝ f)
    (hdfc : Continuous (deriv f)) (M0 M1 : ℝ)
    (hM0 : ∀ x, |f x| ≤ M0) (hM1 : ∀ x, |deriv f x| ≤ M1)
    (R : ℝ) :
    deriv (scaledKernelConvolution h f R) = scaledKernelConvolution h (deriv f) R := by
  funext x
  exact (hasDerivAt_scaledKernelConvolution h f hh hfd hdfc M0 M1 hM0 hM1 R x).deriv

end RiemannResearch.Analysis
