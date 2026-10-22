import RiemannResearch.Analysis.ScaledKernelApproximation
import Mathlib.Analysis.Calculus.MeanValue

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual first-order kernel expansion with a quadratic remainder

A bounded second derivative gives an explicit global quadratic Taylor
remainder by two mean-value estimates. Integrating that estimate against
the actual kernel gives its first-order moment expansion, with a uniform
O(R⁻²) remainder. No asymptotic approximation is assumed.
-/

open MeasureTheory Set
namespace RiemannResearch.Analysis

/-- A first-order Taylor remainder with a convenient (non-sharp) constant. -/
theorem abs_sub_linear_le_sq (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hdf : Differentiable ℝ (deriv f))
    (B : ℝ) (hB : ∀ z, |deriv (deriv f) z| ≤ B) (x t : ℝ) :
    |f (x+t)-f x-deriv f x*t| ≤ B*t^2 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hd (y : ℝ) : |deriv f (x+y)-deriv f x| ≤ B * |y| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := deriv f) (s := univ) (x := x) (y := x+y)
      (fun z _ => hdf z) (fun z _ => by simpa only [Real.norm_eq_abs] using hB z)
      convex_univ (mem_univ _) (mem_univ _)
    simpa only [add_sub_cancel_left, Real.norm_eq_abs] using h
  let g : ℝ → ℝ := fun y => f (x+y)-f x-deriv f x*y
  have hgd (y : ℝ) : HasDerivAt g (deriv f (x+y)-deriv f x) y := by
    have h := ((hf (x+y)).hasDerivAt.comp y ((hasDerivAt_id y).const_add x))
    convert (h.sub_const (f x)).sub ((hasDerivAt_id y).const_mul (deriv f x)) using 1 <;>
      first | rfl | simp only [mul_one]
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := g) (s := Icc (-|t|) |t|) (x := (0:ℝ)) (y := t)
    (fun y _ => (hgd y).differentiableAt)
    (fun y hy => show ‖deriv g y‖ ≤ B * |t| from by
      rw [(hgd y).deriv, Real.norm_eq_abs]
      exact (hd y).trans (mul_le_mul_of_nonneg_left (abs_le.mpr hy) hB0))
    (convex_Icc _ _) ⟨neg_nonpos.mpr (abs_nonneg _),abs_nonneg _⟩
    ⟨neg_abs_le _,le_abs_self _⟩
  have he : g 0 = 0 := by simp only [g,add_zero,sub_self,mul_zero]
  calc
    _ = |g t-g 0| := by rw [he,sub_zero]
    _ ≤ (B * |t|) * |t| := by simpa only [Real.norm_eq_abs,sub_zero] using hm
    _ = B*t^2 := by rw [mul_assoc,←pow_two,sq_abs]

/-- The signed first kernel moment is integrable whenever its absolute moment is. -/
theorem integrable_signed_first_kernel_moment (h : ℝ → ℝ) (hh : Integrable h)
    (hm : Integrable (fun v => |v| * |h v|)) :
    Integrable (fun v : ℝ => v*h v) := by
  apply hm.mono' (continuous_id.aestronglyMeasurable.mul hh.aestronglyMeasurable)
  apply ae_of_all
  intro v
  change ‖v*h v‖ ≤ |v| * |h v|
  simp only [Real.norm_eq_abs,abs_mul,le_refl]

/-- Actual moment expansion of the broad convolution, uniform in x. -/
theorem abs_scaledKernelConvolution_first_order_le (h f : ℝ → ℝ)
    (hh : Integrable h) (hf : Differentiable ℝ f)
    (hdf : Differentiable ℝ (deriv f)) (M B : ℝ)
    (hM : ∀ x, |f x| ≤ M) (hB : ∀ x, |deriv (deriv f) x| ≤ B)
    (hm1 : Integrable (fun v => |v| * |h v|))
    (hm2 : Integrable (fun v => v^2 * |h v|)) (R x : ℝ) :
    |scaledKernelConvolution h f R x-(∫v,h v)*f x+
      ((∫v,v*h v)/R)*deriv f x| ≤
        (B/R^2)*(∫v,v^2 * |h v|) := by
  have hleft := integrable_scaledKernel_integrand h f hh hf.continuous M hM R x
  have hright := hh.mul_const (f x)
  have hfirst := integrable_signed_first_kernel_moment h hh hm1
  have hlin : Integrable (fun v => (v*h v)*(deriv f x/R)) :=
    hfirst.mul_const (deriv f x/R)
  have hsub : Integrable (fun v => h v*f (x-v/R)-h v*f x) := hleft.sub hright
  have he : scaledKernelConvolution h f R x-(∫v,h v)*f x+
      ((∫v,v*h v)/R)*deriv f x =
      ∫v,h v*(f (x-v/R)-f x+(v/R)*deriv f x) := by
    rw [show scaledKernelConvolution h f R x = ∫v,h v*f (x-v/R) from rfl]
    rw [show ((∫v,v*h v)/R)*deriv f x =
      (∫v,v*h v)*(deriv f x/R) by ring]
    rw [←integral_mul_const,←integral_mul_const,
      ←integral_sub hleft hright,←integral_add hsub hlin]
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by ring)
  rw [he]
  calc
    _ ≤ ∫v,(B/R^2)*(v^2 * |h v|) := by
      rw [←Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hm2.const_mul (B/R^2))
      apply ae_of_all
      intro v
      rw [Real.norm_eq_abs,abs_mul]
      have ht := abs_sub_linear_le_sq f hf hdf B hB x (-(v/R))
      have he' : f (x+-(v/R))-f x-deriv f x* (-(v/R)) =
          f (x-v/R)-f x+(v/R)*deriv f x := by ring
      rw [he'] at ht
      calc
        _ ≤ |h v| * (B*(-(v/R))^2) :=
          mul_le_mul_of_nonneg_left ht (abs_nonneg _)
        _ = _ := by rw [neg_sq,div_pow]; ring
    _ = _ := integral_const_mul _ _

end RiemannResearch.Analysis
