import RiemannResearch.Analysis.ScaledKernelApproximation
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual differential broad profiles from a cumulative kernel

The four coefficients are exactly those of
(D²-1/4)(D+1/2)=D³+D²/2-D/4-1/8.
These estimates apply to the scaled actual arithmetic-return profile once
the Abel kernel representation is substituted. No profile convergence,
normalization limit, or uniform bound is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.Analysis

noncomputable def broadKernelProfile (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ) (R x : ℝ) : ℝ :=
  (R⁻¹) ^ 3 * scaledKernelConvolution h (f 3) R x +
    (R⁻¹) ^ 2 / 2 * scaledKernelConvolution h (f 2) R x -
    R⁻¹ / 4 * scaledKernelConvolution h (f 1) R x -
    (1 / 8 : ℝ) * scaledKernelConvolution h (f 0) R x

/-- The derivative array used by the actual broad test. -/
noncomputable def differentialBroadKernelProfile (h φ : ℝ → ℝ) (R x : ℝ) : ℝ :=
  broadKernelProfile h (fun j => iteratedDeriv j φ) R x

private theorem abs_four_terms_le (a b c d x y z w : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    |a*x+b*y-c*z-d*w| ≤ a*|x|+b*|y|+c*|z|+d*|w| := by
  calc
    _ ≤ |a*x+b*y-c*z|+|d*w| := abs_sub _ _
    _ ≤ (|a*x+b*y|+|c*z|)+|d*w| := by linarith [abs_sub (a*x+b*y) (c*z)]
    _ ≤ ((|a*x|+|b*y|)+|c*z|)+|d*w| :=
      by linarith [abs_add_le (a*x) (b*y)]
    _ = _ := by simp only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb,
      abs_of_nonneg hc, abs_of_nonneg hd]

private theorem broad_coefficients {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ t^3 ∧ t^3 ≤ t ∧ 0 ≤ t^2/2 ∧ t^2/2 ≤ t ∧
      0 ≤ t/4 ∧ t/4 ≤ t := by
  have h2 : t^2 ≤ t := by nlinarith
  have h3 : t^3 ≤ t := by
    calc
      t^3 = t * t^2 := by ring
      _ ≤ t*t := mul_le_mul_of_nonneg_left h2 ht0
      _ ≤ t := by nlinarith
  exact ⟨by positivity, h3, by positivity, by nlinarith,
    by positivity, by linarith⟩

private theorem abs_broad_four_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (a b c d : ℝ) :
    |t^3*a+t^2/2*b-t/4*c-(1/8)*d| ≤ |a|+|b|+|c|+|d| := by
  obtain ⟨h30,h31,h20,h21,h10,h11⟩ := broad_coefficients ht0 ht1
  have h := abs_four_terms_le (t^3) (t^2/2) (t/4) (1/8) a b c d
    h30 h20 h10 (by norm_num)
  have ha := mul_le_of_le_one_left (abs_nonneg a) (h31.trans ht1)
  have hb := mul_le_of_le_one_left (abs_nonneg b) (h21.trans ht1)
  have hc := mul_le_of_le_one_left (abs_nonneg c) (h11.trans ht1)
  have hd := mul_le_of_le_one_left (abs_nonneg d) (by norm_num : (1/8:ℝ) ≤ 1)
  linarith

private theorem abs_broad_three_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (a b c : ℝ) :
    |t^3*a+t^2/2*b-t/4*c| ≤ t*(|a|+|b|+|c|) := by
  obtain ⟨h30,h31,h20,h21,h10,h11⟩ := broad_coefficients ht0 ht1
  have h := abs_four_terms_le (t^3) (t^2/2) (t/4) 0 a b c 0
    h30 h20 h10 (by norm_num)
  simp only [mul_zero, sub_zero, abs_zero, add_zero] at h
  have ha := mul_le_mul_of_nonneg_right h31 (abs_nonneg a)
  have hb := mul_le_mul_of_nonneg_right h21 (abs_nonneg b)
  have hc := mul_le_mul_of_nonneg_right h11 (abs_nonneg c)
  nlinarith

/-- Integrability of every member of the actual finite differential family. -/
theorem integrable_broadKernelProfile (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfi : ∀ j, Integrable (f j))
    (hfc : ∀ j, Continuous (f j)) (R : ℝ) :
    Integrable (broadKernelProfile h f R) := by
  have hI (j : ℕ) := integrable_scaledKernelConvolution h (f j) hh (hfi j) (hfc j) R
  exact (((hI 3).const_mul ((R⁻¹)^3)).add ((hI 2).const_mul ((R⁻¹)^2/2))).sub
    ((hI 1).const_mul (R⁻¹/4)) |>.sub ((hI 0).const_mul (1/8))

/-- Exact mean when the three derivative profiles have zero integral. -/
theorem integral_broadKernelProfile (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfi : ∀ j, Integrable (f j))
    (hfc : ∀ j, Continuous (f j))
    (hz1 : (∫ x, f 1 x) = 0) (hz2 : (∫ x, f 2 x) = 0)
    (hz3 : (∫ x, f 3 x) = 0) (R : ℝ) :
    (∫ x, broadKernelProfile h f R x) =
      (-(∫ v, h v) / 8) * ∫ x, f 0 x := by
  have hI (j : ℕ) := integrable_scaledKernelConvolution h (f j) hh (hfi j) (hfc j) R
  have hmean (j : ℕ) := integral_scaledKernelConvolution h (f j) hh (hfi j) (hfc j) R
  have h32 : Integrable (fun x => (R⁻¹)^3*scaledKernelConvolution h (f 3) R x +
      (R⁻¹)^2/2*scaledKernelConvolution h (f 2) R x) :=
    ((hI 3).const_mul _).add ((hI 2).const_mul _)
  have h321 : Integrable (fun x => (R⁻¹)^3*scaledKernelConvolution h (f 3) R x +
      (R⁻¹)^2/2*scaledKernelConvolution h (f 2) R x -
      R⁻¹/4*scaledKernelConvolution h (f 1) R x) :=
    h32.sub ((hI 1).const_mul _)
  unfold broadKernelProfile
  rw [integral_sub h321 ((hI 0).const_mul _),
    integral_sub h32 ((hI 1).const_mul _),
    integral_add ((hI 3).const_mul _) ((hI 2).const_mul _)]
  simp_rw [integral_const_mul, hmean]
  rw [hz1, hz2, hz3]
  ring

/-- One scale-independent L¹ bound for the actual four-term profile. -/
theorem integral_abs_broadKernelProfile_le (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfi : ∀ j, Integrable (f j))
    (hfc : ∀ j, Continuous (f j)) {R : ℝ} (hR : 1 ≤ R) :
    (∫ x, |broadKernelProfile h f R x|) ≤ (∫ v, |h v|) *
      ((∫ x, |f 3 x|)+(∫ x, |f 2 x|)+(∫ x, |f 1 x|)+(∫ x, |f 0 x|)) := by
  have hR0 : 0 < R := by linarith
  have ht0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0.le
  have ht1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hI (j : ℕ) := integrable_scaledKernelConvolution h (f j) hh (hfi j) (hfc j) R
  have hB := integrable_broadKernelProfile h f hh hfi hfc R
  have hbound (j : ℕ) := integral_abs_scaledKernelConvolution_le h (f j) hh
    (hfi j) (hfc j) R
  calc
    _ ≤ ∫ x, |scaledKernelConvolution h (f 3) R x|+
        |scaledKernelConvolution h (f 2) R x|+|scaledKernelConvolution h (f 1) R x|+
        |scaledKernelConvolution h (f 0) R x| := by
      apply integral_mono_ae hB.abs ((((hI 3).abs.add (hI 2).abs).add (hI 1).abs).add (hI 0).abs)
      exact ae_of_all _ (fun x => abs_broad_four_le ht0 ht1 _ _ _ _)
    _ = (∫ x, |scaledKernelConvolution h (f 3) R x|)+
        (∫ x, |scaledKernelConvolution h (f 2) R x|)+
        (∫ x, |scaledKernelConvolution h (f 1) R x|)+
        (∫ x, |scaledKernelConvolution h (f 0) R x|) := by
      have h32 : Integrable (fun x => |scaledKernelConvolution h (f 3) R x| +
          |scaledKernelConvolution h (f 2) R x|) := (hI 3).abs.add (hI 2).abs
      have h321 : Integrable (fun x => |scaledKernelConvolution h (f 3) R x| +
          |scaledKernelConvolution h (f 2) R x| +
          |scaledKernelConvolution h (f 1) R x|) := h32.add (hI 1).abs
      rw [integral_add h321 (hI 0).abs,
        integral_add h32 (hI 1).abs,integral_add (hI 3).abs (hI 2).abs]
    _ ≤ _ := by nlinarith [hbound 0, hbound 1, hbound 2, hbound 3]

/-- One scale-independent sup bound, supplied by actual kernel integration. -/
theorem abs_broadKernelProfile_le (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (M : ℕ → ℝ) (hM : ∀ j x, |f j x| ≤ M j)
    {R : ℝ} (hR : 1 ≤ R) (x : ℝ) :
    |broadKernelProfile h f R x| ≤ (∫ v, |h v|)*(M 3+M 2+M 1+M 0) := by
  have hR0 : 0 < R := by linarith
  have hfour := abs_broad_four_le (inv_nonneg.mpr hR0.le) (inv_le_one_of_one_le₀ hR)
    (scaledKernelConvolution h (f 3) R x) (scaledKernelConvolution h (f 2) R x)
    (scaledKernelConvolution h (f 1) R x) (scaledKernelConvolution h (f 0) R x)
  have hb (j : ℕ) := abs_scaledKernelConvolution_le h (f j) hh (M j) (hM j) R x
  change |broadKernelProfile h f R x| ≤ _ at hfour
  nlinarith [hb 0, hb 1, hb 2, hb 3]

/-- Concrete O(1/R) uniform convergence of the actual differential family. -/
theorem abs_broadKernelProfile_sub_limit_le (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfc : Continuous (f 0))
    (M : ℕ → ℝ) (hM : ∀ j x, |f j x| ≤ M j)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x y, |f 0 x-f 0 y| ≤ K*|x-y|)
    (hmoment : Integrable (fun v => |v| * |h v|))
    {R : ℝ} (hR : 1 ≤ R) (x : ℝ) :
    |broadKernelProfile h f R x - (-(∫ v, h v)/8)*f 0 x| ≤
      ((∫ v, |h v|)*(M 3+M 2+M 1)+K*(∫ v, |v| * |h v|))/R := by
  have hR0 : 0 < R := by linarith
  have ht0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0.le
  have ht1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hsmall := abs_broad_three_le ht0 ht1
    (scaledKernelConvolution h (f 3) R x) (scaledKernelConvolution h (f 2) R x)
    (scaledKernelConvolution h (f 1) R x)
  have hb (j : ℕ) := abs_scaledKernelConvolution_le h (f j) hh (M j) (hM j) R x
  have hbase := abs_scaledKernelConvolution_sub_mass_le h (f 0) hh hfc
    (M 0) K (hM 0) hK hmoment R x
  rw [abs_of_pos hR0] at hbase
  have heq : broadKernelProfile h f R x - (-(∫ v,h v)/8)*f 0 x =
      ((R⁻¹)^3*scaledKernelConvolution h (f 3) R x+
       (R⁻¹)^2/2*scaledKernelConvolution h (f 2) R x-
       R⁻¹/4*scaledKernelConvolution h (f 1) R x) -
       (1/8)*(scaledKernelConvolution h (f 0) R x-(∫ v,h v)*f 0 x) := by
    unfold broadKernelProfile
    ring
  rw [heq]
  have htri := abs_sub
    ((R⁻¹)^3*scaledKernelConvolution h (f 3) R x+
     (R⁻¹)^2/2*scaledKernelConvolution h (f 2) R x-
     R⁻¹/4*scaledKernelConvolution h (f 1) R x)
    ((1/8)*(scaledKernelConvolution h (f 0) R x-(∫v,h v)*f 0 x))
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/8)] at htri
  have hs := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hb 3) (hb 2)) (hb 1)) ht0
  have hm0 : 0 ≤ ∫ v, |v| * |h v| := integral_nonneg (fun v => by positivity)
  simp only [div_eq_mul_inv] at hbase htri hsmall hs ⊢
  nlinarith [mul_nonneg hK0 hm0, mul_nonneg (mul_nonneg hK0 hm0) ht0]

end RiemannResearch.Analysis
