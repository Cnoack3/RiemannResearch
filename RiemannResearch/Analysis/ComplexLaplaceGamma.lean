/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Laplace–Gamma integral with a complex damping parameter

The real-parameter identity is Mathlib's
`Complex.integral_cpow_mul_exp_neg_mul_Ioi` in
`Mathlib.Analysis.SpecialFunctions.Gamma.Basic`:
https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean
This reference supports the starting identity. The extension to the right
half-plane below uses dominated differentiation and the analytic identity theorem.

The concrete RH-program consumer is the complex Mellin kernel for the damped
Estermann series in Baluyot's zero-density argument. All powers use Mathlib's
principal complex-power convention. Neither a Gamma growth estimate nor a
zero-density hypothesis is assumed.
-/

open Set Filter MeasureTheory Complex
open scoped Topology
noncomputable section
namespace Complex

private theorem laplaceGamma_integrand_norm (a z : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (a - 1) * exp (-z * x)‖ =
      x ^ (a.re - 1) * Real.exp (-z.re * x) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, norm_exp]
  simp

/-- Absolute convergence of the Laplace–Gamma integral on both right half-planes. -/
theorem integrableOn_cpow_mul_exp_neg_complex {a z : ℂ} (ha : 0 < a.re)
    (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (a - 1) * exp (-z * x)) (Ioi 0) := by
  have hreal : IntegrableOn (fun x : ℝ => x ^ (a.re - 1) * Real.exp (-z.re * x))
      (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
        (s := a.re - 1) (b := z.re) (by linarith) (by norm_num) hz)
  have hm : AEStronglyMeasurable
      (fun x : ℝ => (x : ℂ) ^ (a - 1) * exp (-z * x)) (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (continuousOn_of_forall_continuousAt (fun x hx =>
      (continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hx)).comp
        continuous_ofReal.continuousAt)).mul ?_
    fun_prop
  refine hreal.mono' hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (laplaceGamma_integrand_norm a z hx).le

private theorem cpow_mul_x {a : ℂ} {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * (x : ℂ) ^ (a - 1) = (x : ℂ) ^ a := by
  calc
    _ = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (a - 1) := by rw [cpow_one]
    _ = (x : ℂ) ^ (1 + (a - 1)) := (cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')).symm
    _ = _ := by congr 1; ring

private theorem differentiableAt_laplaceGamma {a z : ℂ} (ha : 0 < a.re)
    (hz : 0 < z.re) :
    DifferentiableAt ℂ
      (fun z : ℂ => ∫ x : ℝ in Ioi 0, (x : ℂ) ^ (a - 1) * exp (-z * x)) z := by
  let F : ℂ → ℝ → ℂ := fun z x => (x : ℂ) ^ (a - 1) * exp (-z * x)
  let F' : ℂ → ℝ → ℂ := fun z x => -(x : ℂ) * F z x
  let bound : ℝ → ℝ := fun x => x ^ a.re * Real.exp (-(z.re / 2) * x)
  have hm (w : ℂ) : AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (continuousOn_of_forall_continuousAt (fun x hx =>
      (continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hx)).comp
        continuous_ofReal.continuousAt)).mul ?_
    fun_prop
  have hm' : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) :=
    (continuous_ofReal.neg.aestronglyMeasurable).mul (hm z)
  have hb : Integrable bound (volume.restrict (Ioi 0)) := by
    change IntegrableOn (fun x : ℝ => x ^ a.re * Real.exp (-(z.re / 2) * x)) (Ioi (0 : ℝ))
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
        (s := a.re) (b := z.re / 2) (by linarith) (by norm_num) (by linarith))
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := F) (F' := F') (bound := bound)
    (s := {w : ℂ | z.re / 2 < w.re})
    ((isOpen_lt continuous_const continuous_re).mem_nhds (by dsimp; linarith))
    (Filter.Eventually.of_forall hm) (integrableOn_cpow_mul_exp_neg_complex ha hz)
    hm' ?_ hb ?_
  · exact hder.2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx w hw
    dsimp [F', F, bound]
    rw [show -(x : ℂ) * ((x : ℂ) ^ (a - 1) * exp (-w * x)) =
      -(x : ℂ) ^ a * exp (-w * x) by
        calc
          _ = -((x : ℂ) * (x : ℂ) ^ (a - 1)) * exp (-w * x) := by ring
          _ = _ := by rw [cpow_mul_x hx]]
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hx, norm_exp]
    simp only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, mul_zero, sub_zero]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [hw]) hx.le)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx w hw
    dsimp [F, F']
    simpa only [Pi.neg_apply, id_eq, mul_neg, neg_mul, one_mul,
      mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id w).neg.mul_const (x : ℂ)).cexp.const_mul ((x : ℂ) ^ (a - 1)))

/-- The principal-power Laplace–Gamma formula for a complex damping parameter. -/
theorem integral_cpow_mul_exp_neg_complex {a z : ℂ} (ha : 0 < a.re)
    (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (a - 1) * exp (-z * x)) =
      z ^ (-a) * Gamma a := by
  let U : Set ℂ := {w : ℂ | 0 < w.re}
  let F : ℂ → ℂ := fun w => ∫ x : ℝ in Ioi 0, (x : ℂ) ^ (a - 1) * exp (-w * x)
  let G : ℂ → ℂ := fun w => w ^ (-a) * Gamma a
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hF : AnalyticOnNhd ℂ F U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro w hw
    exact (differentiableAt_laplaceGamma ha hw).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ G U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro w hw
    exact ((differentiableAt_id.cpow_const (mem_slitPlane_iff.mpr (Or.inl hw))).mul_const
      (Gamma a)).differentiableWithinAt
  have hreal {r : ℝ} (hr : 0 < r) : F (r : ℂ) = G (r : ℂ) := by
    dsimp [F, G]
    have h := integral_cpow_mul_exp_neg_mul_Ioi ha hr
    simpa only [neg_mul, one_div, inv_cpow_ofReal_nonneg hr.le, cpow_neg] using h
  have hfreal : ∃ᶠ r : ℝ in 𝓝[≠] 1, F (r : ℂ) = G (r : ℂ) := by
    apply Filter.Eventually.frequently
    filter_upwards [((eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds)] with r hr using hreal hr
  have hfreq : ∃ᶠ w : ℂ in 𝓝[≠] 1, F w = G w := by
    rw [frequently_iff_seq_forall] at hfreal ⊢
    obtain ⟨xs, hxs, heq⟩ := hfreal
    refine ⟨fun n => (xs n : ℂ), ?_, heq⟩
    rw [tendsto_nhdsWithin_iff] at hxs ⊢
    constructor
    · simpa only [Function.comp_def, Complex.ofReal_one] using
        continuous_ofReal.continuousAt.tendsto.comp hxs.1
    · simpa using hxs.2
  have hconn : IsPreconnected U := (convex_Ioi (0 : ℝ)).linear_preimage reLm |>.isPreconnected
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hconn
    (z₀ := (1 : ℂ)) (by simp [U]) hfreq hz

end Complex
