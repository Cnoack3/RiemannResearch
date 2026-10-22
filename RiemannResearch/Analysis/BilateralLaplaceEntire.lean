import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The actual bilateral Laplace integral is entire

The hypothesis is absolute exponential integrability with one polynomial
moment. Holomorphy is proved by differentiation under the Bochner integral;
it is not a field of a structure or an input hypothesis.

This file is an unverified candidate. Only the coordinating root agent may
submit it for Lean verification.
-/

open MeasureTheory Set Filter Metric
open scoped Topology

namespace MeasureTheory.BilateralLaplace

noncomputable def kernel (s : ℂ) (y : ℝ) : ℂ :=
  Complex.exp (-s * (y : ℂ))

noncomputable def transform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ y, f y * kernel s y

/-- The half-density convention of the research note. -/
noncomputable def centeredTransform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  transform f (s - 1 / 2)

noncomputable def momentWeight (f : ℝ → ℂ) (a y : ℝ) : ℝ :=
  (1 + |y|) * ‖f y‖ * Real.exp (a * |y|)

def HasExponentialMoments (f : ℝ → ℂ) : Prop :=
  AEStronglyMeasurable f volume ∧
    ∀ a : ℝ, 0 < a → Integrable (momentWeight f a) volume

/-- Pure exponential absolute integrability already supplies the polynomial moment:
`1 + |y| ≤ exp |y|`, so one extra unit of exponential weight is sufficient. -/
theorem hasExponentialMoments_of_weighted_integrable {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume)
    (hi : ∀ a : ℝ, 0 < a →
      Integrable (fun y : ℝ => Real.exp (a * |y|) * ‖f y‖) volume) :
    HasExponentialMoments f := by
  refine ⟨hf, fun a ha => ?_⟩
  have hc₁ : Continuous (fun y : ℝ => 1 + |y|) := by fun_prop
  have hc₂ : Continuous (fun y : ℝ => Real.exp (a * |y|)) := by fun_prop
  have hm : AEStronglyMeasurable (momentWeight f a) volume :=
    (hc₁.aestronglyMeasurable.mul hf.norm).mul hc₂.aestronglyMeasurable
  apply (hi (a + 1) (by linarith)).mono' hm
  apply Filter.Eventually.of_forall
  intro y
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold momentWeight; positivity)]
  calc
    momentWeight f a y ≤
        Real.exp |y| * ‖f y‖ * Real.exp (a * |y|) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (by simpa [add_comm] using Real.add_one_le_exp |y|) (norm_nonneg _))
        (le_of_lt (Real.exp_pos _))
    _ = Real.exp ((a + 1) * |y|) * ‖f y‖ := by
      rw [show (a + 1) * |y| = |y| + a * |y| by ring, Real.exp_add]
      ring

theorem hasExponentialMoments_of_compactSupport {f : ℝ → ℂ}
    (hf : Continuous f) (hcompact : HasCompactSupport f) :
    HasExponentialMoments f := by
  apply hasExponentialMoments_of_weighted_integrable hf.aestronglyMeasurable
  intro a _
  have hnorm : HasCompactSupport (fun y => ‖f y‖) :=
    hcompact.comp_left (g := fun z : ℂ => ‖z‖) (norm_zero)
  have hc : Continuous (fun y : ℝ => Real.exp (a * |y|) * ‖f y‖) := by fun_prop
  exact hc.integrable_of_hasCompactSupport hnorm.mul_left

theorem kernel_norm_le (s : ℂ) (y : ℝ) :
    ‖kernel s y‖ ≤ Real.exp (‖s‖ * |y|) := by
  rw [kernel, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (-s * (y : ℂ)).re = -s.re * y := by simp
    _ ≤ |-s.re * y| := le_abs_self _
    _ = |s.re| * |y| := by simp [abs_mul]
    _ ≤ ‖s‖ * |y| :=
      mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm s) (abs_nonneg y)

theorem kernel_norm_le_of_norm_le {s : ℂ} {a : ℝ} (ha : ‖s‖ ≤ a) (y : ℝ) :
    ‖kernel s y‖ ≤ Real.exp (a * |y|) :=
  (kernel_norm_le s y).trans <| Real.exp_le_exp.mpr <|
    mul_le_mul_of_nonneg_right ha (abs_nonneg y)

theorem integrand_norm_le_weight (f : ℝ → ℂ) {s : ℂ} {a : ℝ}
    (ha : ‖s‖ ≤ a) (y : ℝ) :
    ‖f y * kernel s y‖ ≤ momentWeight f a y := by
  have he := kernel_norm_le_of_norm_le ha y
  have habs : 0 ≤ |y| := abs_nonneg y
  have hn : 0 ≤ ‖f y‖ * Real.exp (a * |y|) := by positivity
  calc
    ‖f y * kernel s y‖ = ‖f y‖ * ‖kernel s y‖ := norm_mul _ _
    _ ≤ ‖f y‖ * Real.exp (a * |y|) :=
      mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ ≤ (1 + |y|) * (‖f y‖ * Real.exp (a * |y|)) := by nlinarith
    _ = momentWeight f a y := by unfold momentWeight; ring

theorem deriv_integrand_norm_le_weight (f : ℝ → ℂ) {s : ℂ} {a : ℝ}
    (ha : ‖s‖ ≤ a) (y : ℝ) :
    ‖-(y : ℂ) * (f y * kernel s y)‖ ≤ momentWeight f a y := by
  have he := kernel_norm_le_of_norm_le ha y
  have habs : 0 ≤ |y| := abs_nonneg y
  have hn : 0 ≤ ‖f y‖ * Real.exp (a * |y|) := by positivity
  calc
    ‖-(y : ℂ) * (f y * kernel s y)‖ =
        |y| * (‖f y‖ * ‖kernel s y‖) := by simp [norm_mul]
    _ ≤ |y| * (‖f y‖ * Real.exp (a * |y|)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he (norm_nonneg _)) habs
    _ ≤ (1 + |y|) * (‖f y‖ * Real.exp (a * |y|)) := by nlinarith
    _ = momentWeight f a y := by unfold momentWeight; ring

theorem integrand_aestronglyMeasurable {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (s : ℂ) :
    AEStronglyMeasurable (fun y => f y * kernel s y) volume := by
  have hk : Continuous (kernel s) := by unfold kernel; fun_prop
  exact hf.mul hk.aestronglyMeasurable

theorem integrable_integrand {f : ℝ → ℂ}
    (hf : HasExponentialMoments f) (s : ℂ) :
    Integrable (fun y => f y * kernel s y) volume := by
  apply (hf.2 (‖s‖ + 1) (by positivity)).mono'
    (integrand_aestronglyMeasurable hf.1 s)
  exact Filter.Eventually.of_forall <|
    integrand_norm_le_weight f (show ‖s‖ ≤ ‖s‖ + 1 by linarith)

theorem hasDerivAt_integrand (f : ℝ → ℂ) (s : ℂ) (y : ℝ) :
    HasDerivAt (fun z : ℂ => f y * kernel z y)
      (-(y : ℂ) * (f y * kernel s y)) s := by
  unfold kernel
  have hlin : HasDerivAt (fun z : ℂ => -z * (y : ℂ)) (-(y : ℂ)) s := by
    simpa using ((hasDerivAt_id s).neg.mul_const (y : ℂ))
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp (-z * (y : ℂ)))
      (Complex.exp (-s * (y : ℂ)) * (-(y : ℂ))) s :=
    (Complex.hasDerivAt_exp _).comp s hlin
  have hmul := hexp.const_mul (f y)
  convert hmul using 1 <;> first | rfl | ring

/-- Differentiation is justified by an explicit integrable bound on a complex ball. -/
theorem hasDerivAt_transform {f : ℝ → ℂ} (hf : HasExponentialMoments f) (s : ℂ) :
    HasDerivAt (transform f)
      (∫ y : ℝ, -(y : ℂ) * (f y * kernel s y)) s := by
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => -(y : ℂ) * (f y * kernel s y)) volume := by
    have hc : Continuous (fun y : ℝ => -(y : ℂ)) := by fun_prop
    exact hc.aestronglyMeasurable.mul (integrand_aestronglyMeasurable hf.1 s)
  have hbound : ∀ᵐ y : ℝ, ∀ z ∈ ball s 1,
      ‖-(y : ℂ) * (f y * kernel z y)‖ ≤ momentWeight f (‖s‖ + 1) y := by
    apply Filter.Eventually.of_forall
    intro y z hz
    have hdist : ‖z - s‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hz
    have hz_norm : ‖z‖ ≤ ‖s‖ + 1 := by
      have ht : ‖z‖ ≤ ‖z - s‖ + ‖s‖ := by
        simpa using norm_add_le (z - s) s
      linarith
    exact deriv_integrand_norm_le_weight f hz_norm y
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y => f y * kernel z y)
    (F' := fun z y => -(y : ℂ) * (f y * kernel z y))
    (bound := momentWeight f (‖s‖ + 1))
    (ball_mem_nhds s (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall (integrand_aestronglyMeasurable hf.1))
    (integrable_integrand hf s) hmeas hbound
    (hf.2 (‖s‖ + 1) (by positivity))
    (Filter.Eventually.of_forall (fun y z _ => hasDerivAt_integrand f z y))).2

theorem differentiable_transform {f : ℝ → ℂ} (hf : HasExponentialMoments f) :
    Differentiable ℂ (transform f) :=
  fun s => (hasDerivAt_transform hf s).differentiableAt

theorem analyticAt_transform {f : ℝ → ℂ} (hf : HasExponentialMoments f) (s : ℂ) :
    AnalyticAt ℂ (transform f) s :=
  (differentiable_transform hf).analyticAt s

theorem differentiable_centeredTransform {f : ℝ → ℂ}
    (hf : HasExponentialMoments f) : Differentiable ℂ (centeredTransform f) := by
  exact (differentiable_transform hf).comp (differentiable_id.sub_const (1 / 2))

theorem hasDerivAt_centeredTransform {f : ℝ → ℂ}
    (hf : HasExponentialMoments f) (s : ℂ) :
    HasDerivAt (centeredTransform f)
      (∫ y : ℝ, -(y : ℂ) * (f y * kernel (s - 1 / 2) y)) s := by
  change HasDerivAt (transform f ∘ fun x : ℂ => x - 1 / 2)
    (∫ y : ℝ, -(y : ℂ) * (f y * kernel (s - 1 / 2) y)) s
  convert (hasDerivAt_transform hf (s - 1 / 2)).comp s
      ((hasDerivAt_id s).sub_const (1 / 2)) using 1 <;>
    first | rfl | simp only [mul_one, id_eq]

theorem analyticAt_centeredTransform {f : ℝ → ℂ}
    (hf : HasExponentialMoments f) (s : ℂ) :
    AnalyticAt ℂ (centeredTransform f) s :=
  (differentiable_centeredTransform hf).analyticAt s

/-- Equality obtained by an absolutely convergent arithmetic calculation on Re(s)>1
extends to the entire plane as soon as the arithmetic expression is regularized to
an entire function. The Laplace side's analyticity is derived from integrability. -/
theorem centeredTransform_eq_of_rightHalfPlane {f : ℝ → ℂ} {G : ℂ → ℂ}
    (hf : HasExponentialMoments f) (hG : Differentiable ℂ G)
    (hmatch : ∀ s : ℂ, 1 < s.re → centeredTransform f s = G s) :
    centeredTransform f = G := by
  have hnhd : {s : ℂ | (1 : ℝ) < s.re} ∈ 𝓝 (2 : ℂ) := by
    apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    norm_num
  have heq : centeredTransform f =ᶠ[𝓝 (2 : ℂ)] G := by
    filter_upwards [hnhd] with s hs
    exact hmatch s hs
  have hfA : AnalyticOnNhd ℂ (centeredTransform f) univ :=
    fun s _ => analyticAt_centeredTransform hf s
  exact AnalyticOnNhd.eq_of_eventuallyEq hfA (fun s _ => hG.analyticAt s) heq

end MeasureTheory.BilateralLaplace
