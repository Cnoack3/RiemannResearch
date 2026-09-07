import RiemannResearch.RH.NymanBroadKernelEnergy

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Strict positivity of the actual broad normalization at every scale

The actual broad mean is m times the nonzero seed mean, with m nonzero by
the positive cumulative kernel mass. The actual squared norm is integrable;
if its integral vanished, the profile would vanish almost everywhere,
contradicting its exact nonzero mean. No eventual restriction is needed.
-/

open MeasureTheory Set
namespace RiemannResearch.RH
open RiemannResearch.Analysis

theorem nymanBroadKernelEnergy_pos (n : ℕ) (hn : 2≤n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x<a,φ x=0) (hb : ∀ x>b,φ x=0)
    (hmass : (∫x,φ x)≠0) (hR : 0<R) :
    0 < broadKernelEnergy (nymanReturnKernel n) (fun j => iteratedDeriv j φ) R := by
  let B := differentialBroadKernelProfile (nymanReturnKernel n) φ R
  have hc := broadProfile_hasCompactSupport_of_bounds ha hb
  have hs := smoothSuperexponentialDecay_differentialBroadKernelProfile n (by omega) hφ ha hb hR
  have hsd : SuperexponentialDecay (fun x => (B x:ℂ)) := by
    simpa only [iteratedDeriv_zero] using hs.2 0
  have hi2 : Integrable (fun x => B x^2) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using
      hsd.integrable_norm_sq hs.1.continuous
  have hmean : (∫x,B x)=(-(∫t,nymanReturnKernel n t)/8)*(∫x,φ x) := by
    simpa only [iteratedDeriv_zero,B,differentialBroadKernelProfile] using
      integral_broadKernelProfile (nymanReturnKernel n) (fun j => iteratedDeriv j φ)
        (integrable_nymanReturnKernel (by omega))
        (broadProfile_integrable_iteratedDeriv hφ hc)
        (broadProfile_continuous_iteratedDeriv hφ)
        (broadProfile_integral_iteratedDeriv_eq_zero hφ hc (by norm_num : 0<1))
        (broadProfile_integral_iteratedDeriv_eq_zero hφ hc (by norm_num : 0<2))
        (broadProfile_integral_iteratedDeriv_eq_zero hφ hc (by norm_num : 0<3)) R
  have hm : -(∫t,nymanReturnKernel n t)/8 ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (integral_nymanReturnKernel_pos hn).ne') (by norm_num)
  change 0 < ∫x,B x^2
  by_contra hpos
  have hz : (∫x,B x^2)=0 := le_antisymm (le_of_not_gt hpos)
    (integral_nonneg (fun x => sq_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (B x)) hi2).mp hz
  have hzero : B =ᵐ[volume] 0 := by
    filter_upwards [hae] with x hx
    exact sq_eq_zero_iff.mp hx
  have hi0 : (∫x,B x)=0 := by
    calc
      _ = ∫_ : ℝ,(0:ℝ) := integral_congr_ae hzero
      _ = 0 := by simp
  exact (mul_ne_zero hm hmass) (hmean.symm.trans hi0)

/-- N_R is positive for every R>0, not merely eventually. -/
theorem nymanBroadNorm_pos (n : ℕ) (hn : 2≤n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x<a,φ x=0) (hb : ∀ x>b,φ x=0)
    (hmass : (∫x,φ x)≠0) (hR : 0<R) : 0 < nymanBroadNorm n φ R :=
  Real.sqrt_pos.mpr (nymanBroadKernelEnergy_pos n hn hφ ha hb hmass hR)

/-- Exact unit squared norm of the scaled real profile at every positive scale. -/
theorem integral_sq_nymanBroadProfile_eq_one (n : ℕ) (hn : 2≤n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x<a,φ x=0) (hb : ∀ x>b,φ x=0)
    (hmass : (∫x,φ x)≠0) (hR : 0<R) :
    (∫x,nymanBroadProfile n φ R x^2)=1 :=
  integral_sq_normalizedBroadKernelProfile _ _ R (nymanBroadNorm_pos n hn hφ ha hb hmass hR)

/-- The physical arithmetic test F_R has exactly unit actual squared L2 norm. -/
theorem integral_norm_sq_nymanNormalizedBroadTest_eq_one (n : ℕ) (hn : 2≤n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x<a,φ x=0) (hb : ∀ x>b,φ x=0)
    (hmass : (∫x,φ x)≠0) (hR : 0<R) :
    (∫y,‖nymanNormalizedBroadTest n φ R y‖^2)=1 := by
  have hN := nymanBroadNorm_pos n hn hφ ha hb hmass hR
  have hN2 : nymanBroadNorm n φ R^2 =
      broadKernelEnergy (nymanReturnKernel n) (fun j => iteratedDeriv j φ) R :=
    Real.sq_sqrt (nymanBroadKernelEnergy_pos n hn hφ ha hb hmass hR).le
  simp only [nymanNormalizedBroadTest,Pi.smul_apply,norm_smul,Real.norm_eq_abs,
    abs_inv,abs_of_pos hN,mul_pow]
  rw [integral_const_mul,integral_norm_sq_nymanBroadTest_eq n (by omega) hφ ha hb hR,←hN2]
  field_simp [hN.ne']

end RiemannResearch.RH
