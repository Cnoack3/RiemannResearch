import RiemannResearch.Analysis.ActualInghamCauchyObservation
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic

/-!
# Removing the pole and localizing the actual Ingham error

Theorem 4 and Corollary 6 of Chourasiya and Simonič,
https://arxiv.org/html/2507.15184v2, apply a holomorphic damping factor
to the actual mollifier error before interpolating. We give its analytic
continuation at the pole, exact norm off the pole, the Gaussian upper
bound on the full vertical lines and its lower bound on the observation
window. The lower bound uses a positive observation height and is uniform
in the real part. No strip interpolation inequality is assumed.
-/
noncomputable section
open Complex MeasureTheory Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.InghamMollifier

/-- The removable continuation of `(s-1)*ζ(s)`. -/
def gabrielRegularZeta (s : ℂ) : ℂ := if s = 1 then 1 else (s-1) * riemannZeta s

@[simp] theorem gabrielRegularZeta_one : gabrielRegularZeta 1 = 1 := by
  simp [gabrielRegularZeta]

private theorem regularZeta_off {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ gabrielRegularZeta s := by
  have hz : AnalyticAt ℂ (fun t : ℂ => (t - 1) * riemannZeta t) s :=
    (analyticAt_id.sub analyticAt_const).mul (analyticAt_riemannZeta hs)
  apply hz.congr
  filter_upwards [compl_singleton_mem_nhds hs] with t ht
  simp [gabrielRegularZeta, show t ≠ 1 from ht]

theorem analyticAt_gabrielRegularZeta (s : ℂ) : AnalyticAt ℂ gabrielRegularZeta s := by
  by_cases hs : s = 1
  · subst s
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact (regularZeta_off hz).differentiableAt
    · rw [continuousAt_iff_punctured_nhds, gabrielRegularZeta_one]
      apply riemannZeta_residue_one.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp [gabrielRegularZeta, show z ≠ 1 from hz]
  · exact regularZeta_off hs

/-- Complex smoothing parameter `b = κ/T²` written as a real scale. -/
def gabrielDampedError (X : ℕ) (b : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((b : ℂ)*s^2) * (gabrielRegularZeta s * mollifier X s - (s-1)) / s

theorem gabrielDampedError_off (X : ℕ) (b : ℝ) {s : ℂ} (hs : s ≠ 1) :
    gabrielDampedError X b s =
      Complex.exp ((b : ℂ)*s^2) * ((s-1)/s) * mollifiedError X s := by
  simp only [gabrielDampedError, gabrielRegularZeta, if_neg hs, mollifiedError]
  ring

@[simp] theorem gabrielDampedError_one (X : ℕ) (b : ℝ) :
    gabrielDampedError X b 1 = Complex.exp (b : ℂ) * mollifier X 1 := by
  simp [gabrielDampedError]

theorem analyticAt_gabrielDampedError (X : ℕ) (b : ℝ) {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ (gabrielDampedError X b) s := by
  have hex : AnalyticAt ℂ (fun z : ℂ => Complex.exp ((b : ℂ) * z^2)) s :=
    (analyticAt_const.mul (analyticAt_id.pow 2)).cexp
  exact (hex.mul (((analyticAt_gabrielRegularZeta s).mul (mollifier_analyticAt X s)).sub
    (analyticAt_id.sub analyticAt_const))).div analyticAt_id hs

/-- Exact norm of the damped Mellin error, with its full multiplicative pole factor. -/
theorem norm_gabrielDampedError (X : ℕ) (b : ℝ) {s : ℂ} (hs : s ≠ 1) :
    ‖gabrielDampedError X b s‖ = Real.exp (b*(s.re^2-s.im^2)) *
      ‖(s-1)/s‖ * ‖mollifiedError X s‖ := by
  rw [gabrielDampedError_off X b hs, norm_mul, norm_mul, Complex.norm_exp]
  congr 3
  simp [pow_two, Complex.mul_re]

theorem gabriel_pole_factor_le {s : ℂ} (hs : 1 / 2 ≤ s.re) : ‖(s-1)/s‖ ≤ 1 := by
  have hsp : s ≠ 0 := by intro h; subst s; norm_num at hs
  rw [norm_div, div_le_one (norm_pos_iff.mpr hsp)]
  have h1 := Complex.sq_norm (s-1)
  have h2 := Complex.sq_norm s
  rw [Complex.normSq_apply] at h1 h2
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h1
  nlinarith [norm_nonneg (s-1), norm_nonneg s]

theorem gabriel_pole_factor_lower {s : ℂ} {H : ℝ} (hH : 0 < H) (hHs : H ≤ |s.im|) :
    1 - 1/H ≤ ‖(s-1)/s‖ := by
  have hsn : H ≤ ‖s‖ := hHs.trans (Complex.abs_im_le_norm _)
  have hs : s ≠ 0 := norm_pos_iff.mp (hH.trans_le hsn)
  have hsplit : (s-1)/s + 1/s = 1 := by field_simp; ring
  have ht := norm_add_le ((s-1)/s) (1/s)
  rw [hsplit, norm_one, show ‖(1:ℂ)/s‖ = 1/‖s‖ by rw [norm_div, norm_one]] at ht
  linarith [one_div_le_one_div_of_le hH hsn]

/-- Upper bound on the Gaussian envelope on every vertical line in the half-strip. -/
theorem gabrielDampedError_gaussian_upper (X : ℕ) (b : ℝ) {s : ℂ}
    (hs : s ≠ 1) (hx : 1 / 2 ≤ s.re) :
    ‖gabrielDampedError X b s‖ ≤
      Real.exp (b*s.re^2) * Real.exp (-b*s.im^2) * ‖mollifiedError X s‖ := by
  rw [norm_gabrielDampedError X b hs, ← Real.exp_add]
  have he : b*s.re^2 + -b*s.im^2 = b*(s.re^2-s.im^2) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (Real.exp_pos _).le (gabriel_pole_factor_le hx)) (norm_nonneg _)

/-- Uniform lower bound throughout the two finite height windows. -/
theorem gabrielDampedError_window_lower (X : ℕ) {b H T : ℝ}
    (hb : 0 ≤ b) (hH : 1 ≤ H) {s : ℂ} (hHs : H ≤ |s.im|) (hsT : |s.im| ≤ T) :
    Real.exp (b*(s.re^2-T^2)) * (1-1/H) * ‖mollifiedError X s‖ ≤
      ‖gabrielDampedError X b s‖ := by
  have hs : s ≠ 1 := by intro he; subst s; simp at hHs; linarith
  have hT := (abs_nonneg s.im).trans hsT
  have hs2 := (sq_le_sq₀ (abs_nonneg s.im) hT).mpr hsT
  rw [sq_abs] at hs2
  rw [norm_gabrielDampedError X b hs]
  have hsub : 0 ≤ 1-1/H := by
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hH
    simpa using sub_nonneg.mpr h
  exact mul_le_mul_of_nonneg_right (mul_le_mul
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hb))
    (gabriel_pole_factor_lower (by linarith) hHs) hsub (Real.exp_pos _).le) (norm_nonneg _)

end RiemannResearch.Analysis.InghamMollifier
