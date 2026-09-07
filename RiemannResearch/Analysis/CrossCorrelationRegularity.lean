import RiemannResearch.Analysis.SuperexponentialDecay
import Mathlib.Analysis.Calculus.MeanValue

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Lipschitz regularity of actual superexponential correlations

Source: the user-provided Nyman--Weil note, section 2. The derivative estimate
supplies the subtraction at zero in the actual gamma integral.
-/

open MeasureTheory Set

namespace RiemannResearch.Analysis

noncomputable section

theorem SuperexponentialDecay.integrable_norm {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hfc : Continuous f) :
    Integrable (fun y : ℝ => ‖f y‖) := by
  simpa using hf.integrable_weighted_norm hfc (a := 0) (by norm_num)

theorem SuperexponentialDecay.integrable_crossCorrelation {f g : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hg : SuperexponentialDecay g)
    (hfc : Continuous f) (hgc : Continuous g) (t : ℝ) :
    Integrable (fun y : ℝ => f (y + t) * star (g y)) := by
  obtain ⟨A, hA, hbound⟩ := hf 1 (by norm_num)
  exact (crossCorrelation_integrable_and_bound hA.le (by norm_num) hfc hgc hbound
    (hg.integrable_weighted_norm hgc (by norm_num)) t).1

/-- An ordinary global derivative bound derived from superexponential decay
of the derivative. No boundedness premise remains in the result. -/
theorem SuperexponentialDecay.exists_deriv_bound {f : ℝ → ℂ}
    (hf : SuperexponentialDecay (deriv f)) :
    ∃ K : ℝ, 0 < K ∧ ∀ y, ‖deriv f y‖ ≤ K := by
  obtain ⟨K, hK, hbound⟩ := hf 1 (by norm_num)
  refine ⟨K, hK, fun y => (hbound y).trans ?_⟩
  have he : Real.exp (-(1 : ℝ) * |y|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := abs_nonneg y; linarith)
  simpa using mul_le_mul_of_nonneg_left he hK.le

theorem crossCorrelation_norm_sub_le {f g : ℝ → ℂ} {K : ℝ}
    (hK : 0 ≤ K)
    (hfi : ∀ t : ℝ, Integrable (fun y : ℝ => f (y + t) * star (g y)))
    (hgi : Integrable (fun y : ℝ => ‖g y‖))
    (hfd : ∀ y z : ℝ, ‖f y - f z‖ ≤ K * |y - z|) (t u : ℝ) :
    ‖crossCorrelation f g t - crossCorrelation f g u‖ ≤
      (K * (∫ y : ℝ, ‖g y‖)) * |t - u| := by
  have hmajor := hgi.const_mul (K * |t - u|)
  have hbound (y : ℝ) :
      ‖f (y + t) * star (g y) - f (y + u) * star (g y)‖ ≤
        (K * |t - u|) * ‖g y‖ := by
    rw [← sub_mul, norm_mul, norm_star]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [add_sub_add_left_eq_sub] using hfd (y + t) (y + u)
  unfold crossCorrelation
  rw [← integral_sub (hfi t) (hfi u)]
  calc
    ‖∫ y : ℝ, f (y + t) * star (g y) - f (y + u) * star (g y)‖ ≤
        ∫ y : ℝ, (K * |t - u|) * ‖g y‖ :=
      norm_integral_le_of_norm_le hmajor (Filter.Eventually.of_forall hbound)
    _ = _ := by rw [integral_const_mul]; ring

/-- The actual correlation is globally Lipschitz when the first test and
its derivative decrease superexponentially. This supplies both continuity
and the local subtraction required by the gamma factor. -/
theorem SuperexponentialDecay.exists_crossCorrelation_lipschitz {f g : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hg : SuperexponentialDecay g)
    (hdf : SuperexponentialDecay (deriv f)) (hfd : Differentiable ℝ f)
    (hgc : Continuous g) :
    ∃ K : NNReal, LipschitzWith K (RiemannResearch.Analysis.crossCorrelation f g) := by
  obtain ⟨A, hA, hbound⟩ := hdf.exists_deriv_bound
  have hslope (y z : ℝ) : ‖f y - f z‖ ≤ A * |y - z| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x (_ : x ∈ (univ : Set ℝ)) => hfd x)
      (fun x (_ : x ∈ (univ : Set ℝ)) => hbound x)
      (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ z) (mem_univ y)
    simpa only [Real.norm_eq_abs] using h
  let K : NNReal := ⟨A * (∫ y : ℝ, ‖g y‖),
    mul_nonneg hA.le (integral_nonneg (fun y => norm_nonneg _))⟩
  refine ⟨K, LipschitzWith.of_dist_le_mul ?_⟩
  intro t u
  rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs]
  change ‖RiemannResearch.Analysis.crossCorrelation f g t -
    RiemannResearch.Analysis.crossCorrelation f g u‖ ≤
      (A * (∫ y : ℝ, ‖g y‖)) * |t - u|
  exact crossCorrelation_norm_sub_le hA.le
    (hf.integrable_crossCorrelation hg hfd.continuous hgc)
    (hg.integrable_norm hgc) hslope t u

end
end RiemannResearch.Analysis
