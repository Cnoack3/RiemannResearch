import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Explicit broad convolution estimates

The scaled kernel operator is the actual Bochner integral. Its L¹ bound,
exact mean, uniform approximation estimate, and squared-norm error are
proved from integrability and the first absolute moment of the kernel.
No convergence of the broad family is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.Analysis

noncomputable def scaledKernelConvolution (h f : ℝ → ℝ) (R x : ℝ) : ℝ :=
  ∫ v, h v * f (x - v / R)

/-- Full product integrability follows by translation in the profile variable. -/
theorem integrable_scaledKernel_product (h f : ℝ → ℝ)
    (hh : Integrable h) (hf : Integrable f) (hfc : Continuous f) (R : ℝ) :
    Integrable (fun p : ℝ × ℝ => h p.2 * f (p.1 - p.2 / R)) (volume.prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => h p.2 * f (p.1 - p.2 / R)) (volume.prod volume) := by
    have hc : Continuous (fun p : ℝ × ℝ => f (p.1 - p.2 / R)) := by fun_prop
    exact hh.aestronglyMeasurable.comp_snd.mul hc.aestronglyMeasurable
  apply (integrable_prod_iff' hm).mpr
  constructor
  · exact ae_of_all _ (fun v => (hf.comp_sub_right (v / R)).const_mul (h v))
  · have he (v : ℝ) : (∫ x, ‖h v * f (x - v / R)‖) =
        |h v| * ∫ x, |f x| := by
      simp_rw [norm_mul, Real.norm_eq_abs]
      rw [integral_const_mul]
      congr 1
      exact integral_sub_right_eq_self (μ := volume) (fun x => |f x|) (v / R)
    simpa only [he] using hh.abs.mul_const (∫ x, |f x|)

/-- The actual broad convolution is integrable. -/
theorem integrable_scaledKernelConvolution (h f : ℝ → ℝ)
    (hh : Integrable h) (hf : Integrable f) (hfc : Continuous f) (R : ℝ) :
    Integrable (scaledKernelConvolution h f R) :=
  (integrable_scaledKernel_product h f hh hf hfc R).integral_prod_left

/-- Exact mean, independent of the scale parameter. -/
theorem integral_scaledKernelConvolution (h f : ℝ → ℝ)
    (hh : Integrable h) (hf : Integrable f) (hfc : Continuous f) (R : ℝ) :
    (∫ x, scaledKernelConvolution h f R x) = (∫ v, h v) * ∫ x, f x := by
  unfold scaledKernelConvolution
  rw [integral_integral_swap (integrable_scaledKernel_product h f hh hf hfc R)]
  simp_rw [integral_const_mul, integral_sub_right_eq_self]
  exact integral_mul_const _ _

/-- An exact scale-independent L¹ bound, derived using Fubini. -/
theorem integral_abs_scaledKernelConvolution_le (h f : ℝ → ℝ)
    (hh : Integrable h) (hf : Integrable f) (hfc : Continuous f) (R : ℝ) :
    (∫ x, |scaledKernelConvolution h f R x|) ≤
      (∫ v, |h v|) * ∫ x, |f x| := by
  have hp := integrable_scaledKernel_product h f hh hf hfc R
  have hH := integrable_scaledKernelConvolution h f hh hf hfc R
  calc
    _ ≤ ∫ x, ∫ v, ‖h v * f (x - v / R)‖ := by
      apply integral_mono_ae hH.abs hp.norm.integral_prod_left
      exact ae_of_all _ (fun x => by
        simpa only [scaledKernelConvolution, Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun v => h v * f (x - v / R)))
    _ = ∫ v, ∫ x, ‖h v * f (x - v / R)‖ := integral_integral_swap hp.norm
    _ = _ := by
      simp_rw [norm_mul, Real.norm_eq_abs, integral_const_mul]
      simp_rw [integral_sub_right_eq_self (μ := volume) (fun x => |f x|)]
      exact integral_mul_const _ _

/-- Every pointwise convolution integral is genuine under a profile bound. -/
theorem integrable_scaledKernel_integrand (h f : ℝ → ℝ)
    (hh : Integrable h) (hfc : Continuous f) (M : ℝ)
    (hM : ∀ x, |f x| ≤ M) (R x : ℝ) :
    Integrable (fun v => h v * f (x - v / R)) := by
  have hm : AEStronglyMeasurable (fun v => h v * f (x - v / R)) volume := by
    have hc : Continuous (fun v => f (x - v / R)) := by fun_prop
    exact hh.aestronglyMeasurable.mul hc.aestronglyMeasurable
  apply (hh.abs.mul_const M).mono' hm
  apply ae_of_all
  intro v
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)

/-- Uniform sup norm control of the actual broad convolution. -/
theorem abs_scaledKernelConvolution_le (h f : ℝ → ℝ)
    (hh : Integrable h) (M : ℝ) (hM : ∀ x, |f x| ≤ M) (R x : ℝ) :
    |scaledKernelConvolution h f R x| ≤ (∫ v, |h v|) * M := by
  unfold scaledKernelConvolution
  calc
    _ ≤ ∫ v, |h v| * M := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hh.abs.mul_const M)
      exact ae_of_all _ (fun v => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _))
    _ = _ := integral_mul_const _ _

/-- The first absolute kernel moment gives a concrete O(1/R) uniform
approximation estimate. This proves convergence of the actual integral. -/
theorem abs_scaledKernelConvolution_sub_mass_le (h f : ℝ → ℝ)
    (hh : Integrable h) (hfc : Continuous f) (M K : ℝ)
    (hM : ∀ x, |f x| ≤ M)
    (hK : ∀ x y, |f x - f y| ≤ K * |x - y|)
    (hmoment : Integrable (fun v => |v| * |h v|)) (R x : ℝ) :
    |scaledKernelConvolution h f R x - (∫ v, h v) * f x| ≤
      (K / |R|) * ∫ v, |v| * |h v| := by
  have hleft := integrable_scaledKernel_integrand h f hh hfc M hM R x
  have hright := hh.mul_const (f x)
  unfold scaledKernelConvolution
  rw [← integral_mul_const, ← integral_sub hleft hright]
  calc
    _ ≤ ∫ v, (K / |R|) * (|v| * |h v|) := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hmoment.const_mul (K / |R|))
      apply ae_of_all
      intro v
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
      calc
        _ ≤ |h v| * (K * |(x - v / R) - x|) :=
          mul_le_mul_of_nonneg_left (hK _ _) (abs_nonneg _)
        _ = _ := by
          rw [show (x - v / R) - x = -(v / R) by ring,
            abs_neg, abs_div]
          ring
    _ = _ := integral_const_mul _ _

/-- Pointwise convergence follows from the explicit uniform estimate. -/
theorem tendsto_scaledKernelConvolution (h f : ℝ → ℝ)
    (hh : Integrable h) (hfc : Continuous f) (M K : ℝ)
    (hM : ∀ x, |f x| ≤ M)
    (hK : ∀ x y, |f x - f y| ≤ K * |x - y|)
    (hmoment : Integrable (fun v => |v| * |h v|)) (x : ℝ) :
    Tendsto (fun R : ℝ => scaledKernelConvolution h f R x) atTop
      (𝓝 ((∫ v, h v) * f x)) := by
  let J : ℝ := ∫ v, |v| * |h v|
  have hlim : Tendsto (fun R : ℝ => (K / R) * J) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_mul] using
      (tendsto_inv_atTop_zero.const_mul K).mul_const J
  have hz : Tendsto (fun R : ℝ => scaledKernelConvolution h f R x -
      (∫ v, h v) * f x) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    simpa only [Real.norm_eq_abs, abs_of_pos hR, J] using
      abs_scaledKernelConvolution_sub_mass_le h f hh hfc M K hM hK hmoment R x
  have h := hz.add_const ((∫ v, h v) * f x)
  simpa only [sub_add_cancel, zero_add] using h

/-- L¹ plus a uniform bound supplies square integrability. -/
theorem integrable_sq_of_integrable_of_abs_le (f : ℝ → ℝ)
    (hf : Integrable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    Integrable (fun x => f x ^ 2) := by
  apply (hf.abs.mul_const M).mono' (hf.aestronglyMeasurable.pow 2)
  apply ae_of_all
  intro x
  change ‖f x ^ 2‖ ≤ |f x| * M
  rw [Real.norm_eq_abs, abs_pow]
  nlinarith [hM x, abs_nonneg (f x)]

/-- A uniform approximation bound and actual L¹ estimates control the
squared norm directly, avoiding an assumed L² convergence statement. -/
theorem abs_integral_sq_sub_le (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g)
    (Mf Mg E : ℝ) (hMf : ∀ x, |f x| ≤ Mf) (hMg : ∀ x, |g x| ≤ Mg)
    (hE : ∀ x, |f x - g x| ≤ E) :
    |(∫ x, f x ^ 2) - ∫ x, g x ^ 2| ≤
      E * ((∫ x, |f x|) + ∫ x, |g x|) := by
  have hf2 := integrable_sq_of_integrable_of_abs_le f hf Mf hMf
  have hg2 := integrable_sq_of_integrable_of_abs_le g hg Mg hMg
  rw [← integral_sub hf2 hg2]
  calc
    _ ≤ ∫ x, E * (|f x| + |g x|) := by
      have hm : Integrable (fun x => E * (|f x| + |g x|)) :=
        (hf.abs.add hg.abs).const_mul E
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hm
      apply ae_of_all
      intro x
      rw [Real.norm_eq_abs,
        show f x ^ 2 - g x ^ 2 = (f x - g x) * (f x + g x) by ring, abs_mul]
      have hE0 : 0 ≤ E := (abs_nonneg (f x - g x)).trans (hE x)
      exact mul_le_mul (hE x) (abs_add_le _ _) (abs_nonneg _) hE0
    _ = _ := by rw [integral_const_mul, integral_add hf.abs hg.abs]

end RiemannResearch.Analysis
