import RiemannResearch.RH.NymanBroadFamily
import RiemannResearch.RH.NymanCompletionAdmissibility
import RiemannResearch.Analysis.CrossCorrelationRegularity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-! # Actual L2 energy and admissibility of the broad arithmetic family -/

open MeasureTheory Set
open scoped Topology
namespace RiemannResearch.Analysis

theorem SuperexponentialDecay.comp_mul_pos {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) {R : ℝ} (hR : 0 < R) :
    SuperexponentialDecay (fun x => f (R * x)) := by
  intro a ha
  obtain ⟨C, hC, hb⟩ := hf (a / R) (div_pos ha hR)
  refine ⟨C, hC, fun x => ?_⟩
  have h := hb (R * x)
  rw [abs_mul, abs_of_pos hR] at h
  have he : -(a / R) * (R * |x|) = -a * |x| := by field_simp [hR.ne'] <;> ring
  rwa [he] at h

theorem SmoothSuperexponentialDecay.comp_mul_pos {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) {R : ℝ} (hR : 0 < R) :
    SmoothSuperexponentialDecay (fun x => f (R * x)) := by
  refine ⟨hf.1.comp (contDiff_const.mul contDiff_id), ?_⟩
  intro j
  have hj : (j : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j).le
  rw [iteratedDeriv_comp_const_smul (hf.1.of_le hj)]
  exact ((hf.2 j).comp_mul_pos hR).const_smul (R ^ j)

theorem SuperexponentialDecay.integrable_norm_sq {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hc : Continuous f) :
    Integrable (fun x : ℝ => ‖f x‖ ^ 2) := by
  have h := (hf.integrable_crossCorrelation hf hc hc 0).norm
  simpa only [add_zero, norm_mul, norm_star, pow_two] using h

end RiemannResearch.Analysis

namespace RiemannResearch.RH
open RiemannResearch.Analysis

/-- The actual broad test, including every derivative, belongs to E. -/
theorem smoothSuperexponentialDecay_nymanBroadTest (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R) :
    SmoothSuperexponentialDecay (nymanBroadTest n φ R) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hret : SmoothSuperexponentialDecay
      (nymanFullReturn n (nymanBroadPotential φ R)) :=
    nymanFullReturn_smooth_and_all_derivatives_decay
      (contDiff_nymanBroadPotential hφ R) (nymanBroadPotential_zero_below ha hR)
      (nymanBroadPotential_zero_above hb hR) n
  exact hret.poleCancellationOperator

theorem smoothSuperexponentialDecay_nymanNormalizedBroadTest (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R) :
    SmoothSuperexponentialDecay (nymanNormalizedBroadTest n φ R) :=
  (smoothSuperexponentialDecay_nymanBroadTest n hn hφ ha hb hR).const_smul _

/-- Fixed-scale smoothness and rapid decay of the actual real broad profile
follow from its exact identity with the scaled arithmetic test. -/
theorem smoothSuperexponentialDecay_differentialBroadKernelProfile
    (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R) :
    SmoothSuperexponentialDecay
      (fun x => (differentialBroadKernelProfile (nymanReturnKernel n) φ R x : ℂ)) := by
  have hbase := smoothSuperexponentialDecay_nymanBroadTest n hn hφ ha hb hR
  have h := (hbase.comp_mul_pos hR).const_smul (Real.sqrt R)
  have he : (Real.sqrt R) • (fun x => nymanBroadTest n φ R (R * x)) =
      (fun x => (differentialBroadKernelProfile (nymanReturnKernel n) φ R x : ℂ)) := by
    funext x
    simp only [Pi.smul_apply, Complex.real_smul]
    exact nymanBroadTest_scaled_eq n hn hφ ha hb hR x
  rwa [he] at h

theorem smoothSuperexponentialDecay_nymanBroadProfile (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R) :
    SmoothSuperexponentialDecay (fun x => (nymanBroadProfile n φ R x : ℂ)) := by
  have hbase := smoothSuperexponentialDecay_nymanNormalizedBroadTest n hn hφ ha hb hR
  have h := (hbase.comp_mul_pos hR).const_smul (Real.sqrt R)
  have he : (Real.sqrt R) • (fun x => nymanNormalizedBroadTest n φ R (R * x)) =
      (fun x => (nymanBroadProfile n φ R x : ℂ)) := by
    funext x
    simp only [Pi.smul_apply, Complex.real_smul]
    exact nymanNormalizedBroadTest_scaled_eq n hn hφ ha hb hR x
  rwa [he] at h

theorem contDiff_nymanBroadProfile (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (nymanBroadProfile n φ R) := by
  have h := smoothSuperexponentialDecay_nymanBroadProfile n hn hφ ha hb hR
  have hc := Complex.reCLM.contDiff.comp h.1
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using hc

/-- Actual real-profile derivatives, with rapid decay proved for every
fixed scale and every derivative order. -/
theorem superexponential_iteratedDeriv_nymanBroadProfile (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R) (j : ℕ) :
    SuperexponentialDecay (iteratedDeriv j (nymanBroadProfile n φ R)) := by
  have hs := smoothSuperexponentialDecay_nymanBroadProfile n hn hφ ha hb hR
  have hc := contDiff_nymanBroadProfile n hn hφ ha hb hR
  have hd := hs.2 j
  rw [iteratedDeriv_real_to_complex hc j] at hd
  intro d hdpos
  obtain ⟨C, hC, hbound⟩ := hd d hdpos
  refine ⟨C, hC, fun x => ?_⟩
  simpa only [Complex.norm_real] using hbound x

/-- The squared norm integral is a genuine integrable quantity. -/
theorem integrable_norm_sq_nymanBroadTest (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R) :
    Integrable (fun y => ‖nymanBroadTest n φ R y‖ ^ 2) := by
  have h := smoothSuperexponentialDecay_nymanBroadTest n hn hφ ha hb hR
  exact h.decay.integrable_norm_sq h.1.continuous

/-- Exact half-density invariance identifies the profile energy with the
actual squared L2 norm of the arithmetic test. -/
theorem integral_norm_sq_nymanBroadTest_eq (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R) :
    (∫ y : ℝ, ‖nymanBroadTest n φ R y‖ ^ 2) =
      broadKernelEnergy (nymanReturnKernel n) (fun j => iteratedDeriv j φ) R := by
  let B : ℝ → ℝ := differentialBroadKernelProfile (nymanReturnKernel n) φ R
  have hp (y : ℝ) : ‖nymanBroadTest n φ R y‖ ^ 2 = (1 / R) * B (y / R) ^ 2 := by
    have h := nymanBroadTest_scaled_eq n hn hφ ha hb hR (y / R)
    have hy : R * (y / R) = y := by field_simp [hR.ne']
    rw [hy] at h
    have hnrm := congrArg (fun z : ℂ => ‖z‖ ^ 2) h
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg R), mul_pow, Real.sq_sqrt hR.le,
      sq_abs] at hnrm
    change R * ‖nymanBroadTest n φ R y‖ ^ 2 = B (y / R) ^ 2 at hnrm
    calc
      _ = B (y / R) ^ 2 / R := (eq_div_iff hR.ne').2 (by nlinarith [hnrm])
      _ = _ := by ring
  calc
    _ = ∫ y : ℝ, (1 / R) * B (y / R) ^ 2 := integral_congr_ae (ae_of_all _ hp)
    _ = (1 / R) * (∫ y : ℝ, B (y / R) ^ 2) := integral_const_mul _ _
    _ = (1 / R) * (|R| * ∫ x : ℝ, B x ^ 2) := by
      congr 1
      exact Measure.integral_comp_div (fun x : ℝ => B x ^ 2) R
    _ = _ := by
      rw [abs_of_pos hR]
      simp only [B, differentialBroadKernelProfile, broadKernelEnergy]
      field_simp [hR.ne']

theorem nymanBroadNorm_eq_actual_L2 (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R) :
    nymanBroadNorm n φ R = Real.sqrt (∫ y : ℝ, ‖nymanBroadTest n φ R y‖ ^ 2) := by
  rw [integral_norm_sq_nymanBroadTest_eq n hn hφ ha hb hR]
  rfl

end RiemannResearch.RH
