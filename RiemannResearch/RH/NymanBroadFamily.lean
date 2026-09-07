import RiemannResearch.RH.NymanBroadKernelBridge
import RiemannResearch.Analysis.BroadKernelUniformBounds

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-! # The concrete broad Nyman family and its normalization -/

open MeasureTheory
namespace RiemannResearch.RH
open RiemannResearch.Analysis

noncomputable def nymanBroadNorm (n : ℕ) (φ : ℝ → ℝ) (R : ℝ) : ℝ :=
  broadKernelNorm (nymanReturnKernel n) (fun j => iteratedDeriv j φ) R

noncomputable def nymanBroadProfile (n : ℕ) (φ : ℝ → ℝ) (R : ℝ) : ℝ → ℝ :=
  normalizedBroadKernelProfile (nymanReturnKernel n) (fun j => iteratedDeriv j φ) R

noncomputable def nymanNormalizedBroadTest (n : ℕ) (φ : ℝ → ℝ) (R : ℝ) : ℝ → ℂ :=
  (nymanBroadNorm n φ R)⁻¹ • nymanBroadTest n φ R

/-- The actual scaled normalized arithmetic channel is the normalized real
kernel profile, including the exact normalization factor. -/
theorem nymanNormalizedBroadTest_scaled_eq (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R) (x : ℝ) :
    (Real.sqrt R : ℂ) * nymanNormalizedBroadTest n φ R (R*x) =
      (nymanBroadProfile n φ R x : ℂ) := by
  have hbroad := nymanBroadTest_scaled_eq n hn hφ ha hb hR x
  unfold nymanNormalizedBroadTest nymanBroadProfile normalizedBroadKernelProfile
  simp only [Pi.smul_apply,Complex.real_smul,Complex.ofReal_div,
    div_eq_mul_inv,Complex.ofReal_inv]
  rw [show (Real.sqrt R : ℂ)*((nymanBroadNorm n φ R : ℂ)⁻¹*
      nymanBroadTest n φ R (R*x)) =
      ((Real.sqrt R : ℂ)*nymanBroadTest n φ R (R*x))*
        (nymanBroadNorm n φ R : ℂ)⁻¹ by ring,hbroad]
  simp only [differentialBroadKernelProfile,nymanBroadNorm,Complex.ofReal_mul,
    Complex.ofReal_inv]

end RiemannResearch.RH
