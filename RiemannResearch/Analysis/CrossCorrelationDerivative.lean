import RiemannResearch.Analysis.CrossCorrelationRegularity
import Mathlib.Analysis.Calculus.ParametricIntegral

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Differentiating the actual cross-correlation

The derivative integrand is dominated by a constant times the actual L¹ norm
of the second function. The constant follows from superexponential decay of
the first derivative, so no derivative/correlation identity is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RiemannResearch.Analysis

theorem hasDerivAt_crossCorrelation_integrand {f g : ℝ → ℂ}
    (hfd : Differentiable ℝ f) (t y : ℝ) :
    HasDerivAt (fun x : ℝ => f (y + x) * star (g y))
      (deriv f (y + t) * star (g y)) t := by
  have hin : HasDerivAt (fun x : ℝ => y + x) (1 : ℝ) t := by
    convert ((hasDerivAt_const t y).add (hasDerivAt_id t)) using 1 <;>
      first | rfl | simp
  have hs : HasDerivAt (fun x : ℝ => f (y + x)) (deriv f (y + t)) t := by
    convert (hfd (y + t)).hasDerivAt.scomp t hin using 1 <;>
      first | rfl | simp
  convert hs.mul_const (star (g y)) using 1 <;> rfl

theorem SuperexponentialDecay.hasDerivAt_crossCorrelation {f g : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hg : SuperexponentialDecay g)
    (hdf : SuperexponentialDecay (deriv f)) (hfd : Differentiable ℝ f)
    (hdfc : Continuous (deriv f)) (hgc : Continuous g) (t : ℝ) :
    HasDerivAt (RiemannResearch.Analysis.crossCorrelation f g)
      (RiemannResearch.Analysis.crossCorrelation (deriv f) g t) t := by
  obtain ⟨A, hA, hbound⟩ := hdf.exists_deriv_bound
  have hmeas (x : ℝ) : AEStronglyMeasurable
      (fun y : ℝ => f (y + x) * star (g y)) volume := by
    have hc : Continuous (fun y : ℝ => f (y + x) * star (g y)) := by
      have hfc := hfd.continuous
      fun_prop
    exact hc.aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable
      (fun y : ℝ => deriv f (y + t) * star (g y)) volume := by
    have hc : Continuous (fun y : ℝ => deriv f (y + t) * star (g y)) := by fun_prop
    exact hc.aestronglyMeasurable
  have hb : ∀ᵐ y : ℝ, ∀ x ∈ (univ : Set ℝ),
      ‖deriv f (y + x) * star (g y)‖ ≤ A * ‖g y‖ := by
    apply ae_of_all
    intro y x _
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_right (hbound (y + x)) (norm_nonneg _)
  have hd : ∀ᵐ y : ℝ, ∀ x ∈ (univ : Set ℝ),
      HasDerivAt (fun t : ℝ => f (y + t) * star (g y))
        (deriv f (y + x) * star (g y)) x :=
    ae_of_all _ (fun y x _ => hasDerivAt_crossCorrelation_integrand hfd x y)
  have hresult := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x y : ℝ => f (y + x) * star (g y))
    (F' := fun x y : ℝ => deriv f (y + x) * star (g y))
    (bound := fun y : ℝ => A * ‖g y‖) (s := univ) (x₀ := t)
    Filter.univ_mem (Filter.Eventually.of_forall hmeas)
    (hf.integrable_crossCorrelation hg hfd.continuous hgc t) hdmeas hb
    ((hg.integrable_norm hgc).const_mul A) hd).2
  convert hresult using 1 <;> rfl

theorem SuperexponentialDecay.deriv_crossCorrelation {f g : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hg : SuperexponentialDecay g)
    (hdf : SuperexponentialDecay (deriv f)) (hfd : Differentiable ℝ f)
    (hdfc : Continuous (deriv f)) (hgc : Continuous g) :
    deriv (RiemannResearch.Analysis.crossCorrelation f g) =
      RiemannResearch.Analysis.crossCorrelation (deriv f) g := by
  funext t
  exact (hf.hasDerivAt_crossCorrelation hg hdf hfd hdfc hgc t).deriv

theorem SuperexponentialDecay.crossCorrelation_deriv {f g : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hg : SuperexponentialDecay g)
    (hdf : SuperexponentialDecay (deriv f)) (hfd : Differentiable ℝ f)
    (hdfc : Continuous (deriv f)) (hgc : Continuous g) :
    SuperexponentialDecay (deriv (RiemannResearch.Analysis.crossCorrelation f g)) := by
  rw [hf.deriv_crossCorrelation hg hdf hfd hdfc hgc]
  exact hdf.crossCorrelation hg hdfc hgc

end RiemannResearch.Analysis
