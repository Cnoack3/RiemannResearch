import RiemannResearch.Analysis.ScaledKernelDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual real autocorrelation variation and its quadratic origin bound

Reflection identifies the actual correlation with the actual scaled kernel
integral. Its derivatives and their L¹ estimates therefore follow from
Fubini and dominated differentiation. Evenness kills the derivative at zero;
two applications of the mean-value bound give the quadratic estimate.
-/

open MeasureTheory Set

namespace RiemannResearch.Analysis

noncomputable def realKernelCorrelation (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ y, f (y + t) * g y

theorem realKernelCorrelation_eq_scaledKernelConvolution (f g : ℝ → ℝ) :
    realKernelCorrelation f g = scaledKernelConvolution (fun y => g (-y)) f 1 := by
  funext t
  unfold realKernelCorrelation scaledKernelConvolution
  rw [← integral_neg_eq_self (fun y : ℝ => f (y + t) * g y) volume]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by simp only [div_one, sub_eq_add_neg, add_comm, mul_comm])

theorem integrable_realKernelCorrelation (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g) (hfc : Continuous f) :
    Integrable (realKernelCorrelation f g) := by
  rw [realKernelCorrelation_eq_scaledKernelConvolution]
  exact integrable_scaledKernelConvolution _ _ hg.comp_neg hf hfc 1

theorem integral_abs_realKernelCorrelation_le (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g) (hfc : Continuous f) :
    (∫ t, |realKernelCorrelation f g t|) ≤ (∫ y, |f y|) * ∫ y, |g y| := by
  rw [realKernelCorrelation_eq_scaledKernelConvolution]
  have hb := integral_abs_scaledKernelConvolution_le (fun y => g (-y)) f
    hg.comp_neg hf hfc 1
  rw [integral_neg_eq_self (fun y => |g y|) volume] at hb
  simpa only [mul_comm] using hb

theorem hasDerivAt_realKernelCorrelation (f g : ℝ → ℝ)
    (hg : Integrable g) (hfd : Differentiable ℝ f)
    (hdfc : Continuous (deriv f)) (M0 M1 : ℝ)
    (hM0 : ∀ x, |f x| ≤ M0) (hM1 : ∀ x, |deriv f x| ≤ M1) (t : ℝ) :
    HasDerivAt (realKernelCorrelation f g) (realKernelCorrelation (deriv f) g t) t := by
  rw [realKernelCorrelation_eq_scaledKernelConvolution,
    realKernelCorrelation_eq_scaledKernelConvolution]
  exact hasDerivAt_scaledKernelConvolution _ _ hg.comp_neg hfd hdfc M0 M1 hM0 hM1 1 t

theorem deriv_realKernelCorrelation (f g : ℝ → ℝ)
    (hg : Integrable g) (hfd : Differentiable ℝ f)
    (hdfc : Continuous (deriv f)) (M0 M1 : ℝ)
    (hM0 : ∀ x, |f x| ≤ M0) (hM1 : ∀ x, |deriv f x| ≤ M1) :
    deriv (realKernelCorrelation f g) = realKernelCorrelation (deriv f) g := by
  funext t
  exact (hasDerivAt_realKernelCorrelation f g hg hfd hdfc M0 M1 hM0 hM1 t).deriv

theorem integral_abs_deriv_realKernelCorrelation_le (f g : ℝ → ℝ)
    (hg : Integrable g) (hdf : Integrable (deriv f)) (hfd : Differentiable ℝ f)
    (hdfc : Continuous (deriv f)) (M0 M1 : ℝ)
    (hM0 : ∀ x, |f x| ≤ M0) (hM1 : ∀ x, |deriv f x| ≤ M1) :
    Integrable (deriv (realKernelCorrelation f g)) ∧
    (∫ t, |deriv (realKernelCorrelation f g) t|) ≤
      (∫ y, |deriv f y|) * ∫ y, |g y| := by
  rw [deriv_realKernelCorrelation f g hg hfd hdfc M0 M1 hM0 hM1]
  exact ⟨integrable_realKernelCorrelation _ _ hdf hg hdfc,
    integral_abs_realKernelCorrelation_le _ _ hdf hg hdfc⟩

theorem abs_realKernelCorrelation_le (f g : ℝ → ℝ)
    (hg : Integrable g) (M : ℝ) (hM : ∀ x, |f x| ≤ M) (t : ℝ) :
    |realKernelCorrelation f g t| ≤ M * ∫ y, |g y| := by
  rw [realKernelCorrelation_eq_scaledKernelConvolution]
  have hb := abs_scaledKernelConvolution_le (fun y => g (-y)) f hg.comp_neg M hM 1 t
  rw [integral_neg_eq_self (fun y => |g y|) volume] at hb
  simpa only [mul_comm] using hb

theorem realKernelCorrelation_self_neg (f : ℝ → ℝ) (t : ℝ) :
    realKernelCorrelation f f (-t) = realKernelCorrelation f f t := by
  unfold realKernelCorrelation
  rw [← integral_add_right_eq_self (fun y : ℝ => f (y + -t) * f y) t]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by simp only [add_neg_cancel_right, mul_comm])

theorem deriv_zero_of_even {c : ℝ → ℝ} (hc : Differentiable ℝ c)
    (heven : ∀ t, c (-t) = c t) : deriv c 0 = 0 := by
  have hin : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) 0 := by
    convert (hasDerivAt_id (0 : ℝ)).neg using 1 <;> rfl
  have hneg : HasDerivAt (fun t : ℝ => c (-t)) (-deriv c 0) 0 := by
    convert (hc (-(0 : ℝ))).hasDerivAt.comp 0 hin using 1 <;>
      first | rfl | simp
  have heq : (fun t : ℝ => c (-t)) = c := funext heven
  rw [heq] at hneg
  have hu := hneg.unique (hc 0).hasDerivAt
  linarith

theorem abs_sub_origin_le_sq_of_even {c : ℝ → ℝ}
    (hc : Differentiable ℝ c) (hdc : Differentiable ℝ (deriv c))
    (heven : ∀ t, c (-t) = c t) (B : ℝ)
    (hB : ∀ t, |deriv (deriv c) t| ≤ B) (t : ℝ) :
    |c 0 - c t| ≤ B * t ^ 2 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hd0 := deriv_zero_of_even hc heven
  have hdb (x : ℝ) : |deriv c x| ≤ B * |x| := by
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := deriv c) (s := univ) (x := (0 : ℝ)) (y := x)
      (fun y _ => hdc y) (fun y _ => by simpa only [Real.norm_eq_abs] using hB y)
      convex_univ (mem_univ _) (mem_univ _)
    simpa only [hd0, sub_zero, Real.norm_eq_abs] using hh
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := c) (s := Icc (-|t|) |t|) (x := (0 : ℝ)) (y := t)
    (fun y _ => hc y)
    (fun y hy => show ‖deriv c y‖ ≤ B * |t| from by
      rw [Real.norm_eq_abs]
      exact (hdb y).trans (mul_le_mul_of_nonneg_left (abs_le.mpr hy) hB0))
    (convex_Icc _ _) ⟨neg_nonpos.mpr (abs_nonneg _), abs_nonneg _⟩
    ⟨neg_abs_le _, le_abs_self _⟩
  calc
    |c 0 - c t| = |c t - c 0| := abs_sub_comm _ _
    _ ≤ (B * |t|) * |t| := by simpa only [Real.norm_eq_abs, sub_zero] using hm
    _ = B * |t| ^ 2 := by ring
    _ = B * t ^ 2 := by rw [sq_abs]

theorem abs_realKernelCorrelation_sub_origin_le_sq (f : ℝ → ℝ)
    (hf : Integrable f) (hfd : Differentiable ℝ f)
    (hdfd : Differentiable ℝ (deriv f)) (hddfc : Continuous (deriv (deriv f)))
    (M0 M1 M2 : ℝ) (hM0 : ∀ x, |f x| ≤ M0)
    (hM1 : ∀ x, |deriv f x| ≤ M1) (hM2 : ∀ x, |deriv (deriv f) x| ≤ M2) (t : ℝ) :
    |realKernelCorrelation f f 0 - realKernelCorrelation f f t| ≤
      (M2 * ∫ y, |f y|) * t ^ 2 := by
  have he := deriv_realKernelCorrelation f f hf hfd hdfd.continuous M0 M1 hM0 hM1
  have he' := deriv_realKernelCorrelation (deriv f) f hf hdfd hddfc M1 M2 hM1 hM2
  apply abs_sub_origin_le_sq_of_even
    (fun x => (hasDerivAt_realKernelCorrelation f f hf hfd hdfd.continuous
      M0 M1 hM0 hM1 x).differentiableAt)
  · rw [he]
    exact fun x => (hasDerivAt_realKernelCorrelation (deriv f) f hf hdfd hddfc
      M1 M2 hM1 hM2 x).differentiableAt
  · exact realKernelCorrelation_self_neg f
  · intro x
    rw [he, he']
    exact abs_realKernelCorrelation_le _ _ hf M2 hM2 x

end RiemannResearch.Analysis
