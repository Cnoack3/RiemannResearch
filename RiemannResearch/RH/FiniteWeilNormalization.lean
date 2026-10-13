import RiemannResearch.LinearAlgebra.ShiftedSchurCertificate
import RiemannResearch.RH.WeilArchimedeanNormalization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite-support archimedean normalization correction

Source: user-provided `RH_Early_Operator_Algebra_Program_Critical_Audit_2026-10-12`,
sections 3--4 and 20. This formalizes its integral correction and exact loss of
coercivity. It does not certify Fourier coefficients or endpoint Weil positivity.
The existing gamma kernel and regulator fix the arithmetic normalization.
-/

open MeasureTheory Set

namespace RiemannResearch.RH.SignedWeilCorrelation

noncomputable section

theorem continuous_archimedeanCorrection : Continuous archimedeanCorrection := by
  unfold archimedeanCorrection
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    positivity

theorem archimedeanCorrection_pos (t : ℝ) : 0 < archimedeanCorrection t := by
  unfold archimedeanCorrection
  positivity

/-- The exact identity shift at nonnegative support length `L`. -/
def finiteNormalizationShift (L : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..L, archimedeanCorrection t

/-- The integral itself, rather than an assumed coefficient formula, gives the shift. -/
theorem finiteNormalizationShift_eq_primitive (L : ℝ) :
    finiteNormalizationShift L =
      archimedeanCorrectionPrimitive 0 - archimedeanCorrectionPrimitive L := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_archimedeanCorrectionPrimitive t)
    (continuous_archimedeanCorrection.neg.intervalIntegrable (μ := volume) 0 L)
  rw [intervalIntegral.integral_neg] at h
  unfold finiteNormalizationShift
  linarith

/-- Closed formula with `r = exp(-L/2)`, matching equation (4.3) of the audit. -/
theorem finiteNormalizationShift_closed (L : ℝ) :
    finiteNormalizationShift L = Real.log 2 + Real.pi / 2 -
      2 * Real.log (1 + Real.exp (-L / 2)) +
      Real.log (1 + Real.exp (-L / 2) ^ 2) -
      2 * Real.arctan (Real.exp (-L / 2)) := by
  rw [finiteNormalizationShift_eq_primitive, archimedeanCorrectionPrimitive_zero]
  unfold archimedeanCorrectionPrimitive
  ring

theorem finiteNormalizationShift_pos {L : ℝ} (hL : 0 < L) :
    0 < finiteNormalizationShift L := by
  apply intervalIntegral.integral_pos hL continuous_archimedeanCorrection.continuousOn
  · intro t _
    exact (archimedeanCorrection_pos t).le
  · exact ⟨0, ⟨le_rfl, hL.le⟩, archimedeanCorrection_pos 0⟩

/-- A rational lower bound for the correction kernel through `L = log 4`. -/
theorem half_le_archimedeanCorrection {y : ℝ} (hy : 0 ≤ y)
    (hy2 : y ≤ 2 * Real.log 2) : 1 / 2 ≤ archimedeanCorrection y := by
  let t := Real.exp (-y / 2)
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have ht2 : (1 / 2 : ℝ) ≤ t := by
    rw [← he]
    exact Real.exp_le_exp.mpr (by linarith)
  change 1 / 2 ≤ 2 * t / ((1 + t) * (1 + t ^ 2))
  have hD : 0 < (1 + t) * (1 + t ^ 2) := by positivity
  have hquad : 0 ≤ t ^ 2 + 2 * t - 1 := by nlinarith [sq_nonneg t]
  have hp := mul_nonneg (sub_nonneg.mpr ht1) hquad
  apply (le_div_iff₀ hD).2
  nlinarith [hp]

theorem half_length_le_finiteNormalizationShift {L : ℝ} (hL : 0 ≤ L)
    (hL2 : L ≤ 2 * Real.log 2) : L / 2 ≤ finiteNormalizationShift L := by
  have h := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun _ : ℝ => (1 / 2 : ℝ)) hL
    (continuous_const.intervalIntegrable 0 L)
    (continuous_archimedeanCorrection.intervalIntegrable 0 L)
    (fun y hy => half_le_archimedeanCorrection hy.1 (hy.2.trans hL2))
  simpa [finiteNormalizationShift, intervalIntegral.integral_const, div_eq_mul_inv] using h

/-- The kernel/regularizer convention is exactly the standard numerator,
including its unscaled subtraction at zero. -/
theorem weilGammaKernel_standard_numerator (φ : ℝ → ℝ) (t : ℝ) :
    weilGammaKernel t * (φ t - weilRegulator t * φ 0) =
      (Real.exp (t / 2) * φ t - φ 0) / (Real.exp t - Real.exp (-t)) := by
  have he : Real.exp (t / 2) * weilRegulator t = 1 := by
    unfold weilRegulator
    rw [← Real.exp_add, show t / 2 + -t / 2 = 0 by ring, Real.exp_zero]
  unfold weilGammaKernel
  calc
    Real.exp (t / 2) / (Real.exp t - Real.exp (-t)) *
        (φ t - weilRegulator t * φ 0) =
      (Real.exp (t / 2) * φ t -
        (Real.exp (t / 2) * weilRegulator t) * φ 0) /
          (Real.exp t - Real.exp (-t)) := by ring
    _ = _ := by rw [he, one_mul]

/-- The two regularizations differ pointwise by precisely the continuous kernel. -/
theorem finite_gamma_integrand_difference (φ : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    weilGammaKernel t * (φ t - weilRegulator t * φ 0) -
      weilGammaKernel t * (φ t - φ 0) =
        (φ 0 / 2) * archimedeanCorrection t := by
  rw [archimedeanCorrection_eq_kernel ht]
  ring

/-- Exact integral discrepancy, with both integrability obligations explicit. -/
theorem finite_gamma_integral_difference (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hgood : IntegrableOn
      (fun t => weilGammaKernel t * (φ t - weilRegulator t * φ 0)) (Ioc 0 L))
    (hbad : IntegrableOn
      (fun t => weilGammaKernel t * (φ t - φ 0)) (Ioc 0 L)) :
    (∫ t in Ioc 0 L, weilGammaKernel t * (φ t - weilRegulator t * φ 0)) -
      (∫ t in Ioc 0 L, weilGammaKernel t * (φ t - φ 0)) =
        (φ 0 / 2) * finiteNormalizationShift L := by
  rw [finiteNormalizationShift, intervalIntegral.integral_of_le hL,
    ← integral_sub hgood hbad, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact finite_gamma_integrand_difference φ ht.1

/-- `common` retains the same poles, prime terms, and endpoint subtraction in
both formulas. At an autocorrelation, `φ 0 = 2 * squaredNorm`. -/
theorem finite_weil_value_shift (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hgood : IntegrableOn
      (fun t => weilGammaKernel t * (φ t - weilRegulator t * φ 0)) (Ioc 0 L))
    (hbad : IntegrableOn
      (fun t => weilGammaKernel t * (φ t - φ 0)) (Ioc 0 L))
    (common squaredNorm : ℝ) (hzero : φ 0 = 2 * squaredNorm) :
    common - (∫ t in Ioc 0 L, weilGammaKernel t * (φ t - φ 0)) =
      (common - (∫ t in Ioc 0 L,
        weilGammaKernel t * (φ t - weilRegulator t * φ 0))) +
      finiteNormalizationShift L * squaredNorm := by
  have h := finite_gamma_integral_difference φ hL hgood hbad
  rw [hzero] at h ⊢
  linarith

/-- A shifted whole-form lower bound transfers with exactly the missing shift. -/
theorem finite_weil_lower_bound_iff {ι : Type*} (q qzip weight : ι → ℝ)
    (L m : ℝ)
    (hshift : ∀ v, qzip v = q v + finiteNormalizationShift L * weight v) :
    (∀ v, m * weight v ≤ qzip v) ↔
      (∀ v, (m - finiteNormalizationShift L) * weight v ≤ q v) := by
  constructor
  · intro h v
    have hv := h v
    rw [hshift v] at hv
    nlinarith
  · intro h v
    have hv := h v
    rw [hshift v]
    nlinarith

/-- Concrete consumer of the corrected core/tail certificate. The common terms
are retained exactly. The envelope and two numerical inequalities are explicit
obligations; this theorem supplies no arithmetic positivity provider. -/
theorem finite_weil_lower_bound_of_block_envelope
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hgood : IntegrableOn
      (fun t => weilGammaKernel t * (φ t - weilRegulator t * φ 0)) (Ioc 0 L))
    (hbad : IntegrableOn
      (fun t => weilGammaKernel t * (φ t - φ 0)) (Ioc 0 L))
    (common a c h ell x y : ℝ) (hzero : φ 0 = 2 * (x ^ 2 + y ^ 2))
    (henvelope : RiemannResearch.LinearAlgebra.blockQuadratic a (-h) c x y ≤
      common - (∫ t in Ioc 0 L, weilGammaKernel t * (φ t - φ 0)))
    (htail : 0 < c - finiteNormalizationShift L - ell)
    (hbudget : h ^ 2 ≤ (a - finiteNormalizationShift L - ell) *
      (c - finiteNormalizationShift L - ell)) :
    ell * (x ^ 2 + y ^ 2) ≤ common -
      (∫ t in Ioc 0 L, weilGammaKernel t * (φ t - weilRegulator t * φ 0)) := by
  have hs := finite_weil_value_shift φ hL hgood hbad common (x ^ 2 + y ^ 2) hzero
  exact RiemannResearch.LinearAlgebra.lower_bound_of_shifted_envelope
    _ _ a c h (finiteNormalizationShift L) ell x y henvelope (by linarith) htail hbudget

end
end RiemannResearch.RH.SignedWeilCorrelation
