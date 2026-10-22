import RiemannResearch.RH.ActualRieszTwoConvolution
import RiemannResearch.RH.ChebyshevMellin
import RiemannResearch.RH.AnnularZeroSpectralTargets
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Actual second-Riesz Mellin transform in its convergent half-plane

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

This module proves the analytic bridge for the actual von Mangoldt sum, using
the finite convolution identity in `ActualRieszTwoConvolution`. No zero location
or explicit formula is assumed. The half-plane `1 < s.re` is retained.

The uncentered sum is crucial: it vanishes below 1. Its dilations therefore have
no omitted boundary integral. The centered sum equals `-x/3` below 1, so its
integral on `Ioi 1` cannot be dilated by the same boundary-free argument.

Proof APIs are source-reviewed at mathlib revision
51e6992efd06126df61a496bebf8f49482a4e129:
`Mathlib.Analysis.MellinTransform`, `Mathlib.MeasureTheory.Integral.Prod`,
and `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.ActualRieszTwo
open ChebyshevMellin

private def psiComplex (x : ℝ) : ℂ := (Chebyshev.psi x : ℂ)

/-- The actual Chebyshev function already is its zero extension below 1. -/
private theorem psiComplex_zero {x : ℝ} (hx : x ≤ 1) : psiComplex x = 0 := by
  simp [psiComplex, Chebyshev.psi_eq_zero_of_le_one hx]

private theorem psi_mellin_zero_extension_integrable {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent psiComplex (-s) := by
  have hi : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-(s + 1)) * psiComplex x) (Ioi 1) := by
    simpa only [psiComplex, mul_comm] using psi_mellin_integrable hs
  have hz : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-(s + 1)) * psiComplex x) (Ioi 0) :=
    hi.of_forall_sdiff_eq_zero measurableSet_Ioi (fun x hx => by
      have hx1 : x ≤ 1 := le_of_not_gt hx.2
      simp [psiComplex_zero hx1])
  simpa only [MellinConvergent, smul_eq_mul,
    show -s - 1 = -(s + 1) by ring] using hz

private theorem psi_mellin_zero_extension (s : ℂ) :
    mellin psiComplex (-s) =
      ∫ x in Ioi (1 : ℝ), (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  simp only [mellin, smul_eq_mul, show -s - 1 = -(s + 1) by ring]
  calc
    _ = ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-(s + 1)) * psiComplex x := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
      intro x hx
      simp [psiComplex_zero (le_of_not_gt hx.2)]
    _ = _ := by simp only [psiComplex, mul_comm]

/-- Exact positive dilation of the uncentered Chebyshev transform. -/
private theorem psi_scaled_mellin {s : ℂ} {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    (∫ x in Ioi (1 : ℝ), (Chebyshev.psi (x * u) : ℂ) *
      (x : ℂ) ^ (-(s + 1))) =
      (u : ℂ) ^ s *
        ∫ x in Ioi (1 : ℝ), (Chebyshev.psi x : ℂ) *
          (x : ℂ) ^ (-(s + 1)) := by
  have hext : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(s + 1)) *
      psiComplex (u * x)) =
      ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-(s + 1)) * psiComplex (u * x) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
    intro x hx
    have hx1 : x ≤ 1 := le_of_not_gt hx.2
    have hux : u * x ≤ 1 := (mul_le_mul_of_nonneg_left hx1 hu0.le).trans
      (by simpa using hu1)
    simp [psiComplex_zero hux]
  calc
    _ = mellin (fun x => psiComplex (u * x)) (-s) := by
      simp only [mellin, smul_eq_mul, show -s - 1 = -(s + 1) by ring]
      rw [hext]
      simp only [psiComplex, mul_comm]
    _ = (u : ℂ) ^ s * mellin psiComplex (-s) := by
      simpa only [neg_neg, smul_eq_mul] using mellin_comp_mul_left psiComplex (-s) hu0
    _ = _ := by rw [psi_mellin_zero_extension]

private def jointKernel (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  ((2 * (1 - p.2) : ℝ) : ℂ) * (Chebyshev.psi (p.1 * p.2) : ℂ) *
    (p.1 : ℂ) ^ (-(s + 1))

/-- An unconditional integrable majorant justifies Fubini on the full tail. -/
private theorem jointKernel_integrable {s : ℂ} (hs : 1 < s.re) :
    Integrable (jointKernel s)
      ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  have hmψ : Measurable (fun p : ℝ × ℝ => Chebyshev.psi (p.1 * p.2)) :=
    psi_measurable.comp (measurable_fst.mul measurable_snd)
  have hm : Measurable (jointKernel s) := by
    unfold jointKernel
    exact ((Complex.continuous_ofReal.measurable.comp
      ((measurable_const.sub measurable_snd).const_mul 2)).mul
      (Complex.continuous_ofReal.measurable.comp hmψ)).mul
        ((Complex.continuous_ofReal.measurable.comp measurable_fst).pow_const _)
  have hi : IntegrableOn (fun x : ℝ => 2 * (Real.log 4 + 4) * x ^ (-s.re))
      (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul _
  have hmajor := hi.comp_fst (volume.restrict (Ioc (0 : ℝ) 1))
  apply hmajor.mono' hm.aestronglyMeasurable
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioc)] with p hp
  have hx0 : 0 < p.1 := lt_trans zero_lt_one hp.1
  have hu0 : 0 ≤ p.2 := hp.2.1.le
  have hu1 : p.2 ≤ 1 := hp.2.2
  have hC : 0 ≤ Real.log 4 + 4 := by positivity
  have hpψ : 0 ≤ Chebyshev.psi (p.1 * p.2) := Chebyshev.psi_nonneg _
  have hψ : Chebyshev.psi (p.1 * p.2) ≤ (Real.log 4 + 4) * p.1 := by
    exact (Chebyshev.psi_le_const_mul_self (mul_nonneg hx0.le hu0)).trans
      (mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul_of_nonneg_left hu1 hx0.le) hC)
  have hweight : 0 ≤ 2 * (1 - p.2) := by linarith
  have hweight2 : 2 * (1 - p.2) ≤ 2 := by linarith
  have he : p.1 * p.1 ^ (-(s.re + 1)) = p.1 ^ (-s.re) := by
    calc
      _ = p.1 ^ (1 : ℝ) * p.1 ^ (-(s.re + 1)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
  simp only [jointKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (sub_nonneg.mpr hu1), abs_of_nonneg hweight, abs_of_nonneg hpψ,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.neg_re,
    Complex.add_re, Complex.one_re]
  calc
    _ ≤ (2 * ((Real.log 4 + 4) * p.1)) * p.1 ^ (-(s.re + 1)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hweight2 hψ hpψ (by norm_num)) (Real.rpow_nonneg hx0.le _)
    _ = _ := by
      rw [mul_assoc, mul_assoc, he]
      ring

private theorem cpow_integral_unit {s : ℂ} (hs : -1 < s.re) :
    (∫ u in Ioc (0 : ℝ) 1, (u : ℂ) ^ s) = 1 / (s + 1) := by
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith
  rw [← intervalIntegral.integral_of_le zero_le_one,
    _root_.integral_cpow (Or.inl hs)]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, Complex.one_cpow,
    Complex.zero_cpow hs1, sub_zero]

/-- The exact beta factor requires only Re(s)>-1. -/
private theorem beta_moment {s : ℂ} (hs : -1 < s.re) :
    (∫ u in Ioc (0 : ℝ) 1,
      ((2 * (1 - u) : ℝ) : ℂ) * (u : ℂ) ^ s) =
      2 / ((s + 1) * (s + 2)) := by
  have hi0 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ s) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_cpow' hs
  have hs' : -1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hi1 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s + 1)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_cpow' hs'
  have h1 : s + 1 ≠ 0 := by
    intro h; have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr; linarith
  have h2 : s + 2 ≠ 0 := by
    intro h; have hr := congrArg Complex.re h
    change s.re + 2 = 0 at hr
    linarith
  calc
    _ = ∫ u in Ioc (0 : ℝ) 1, (2 : ℂ) * ((u : ℂ) ^ s - (u : ℂ) ^ (s + 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only
      rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.1.ne'), Complex.cpow_one]
      push_cast
      ring
    _ = 2 * (1 / (s + 1) - 1 / (s + 2)) := by
      rw [integral_const_mul, integral_sub hi0 hi1,
        cpow_integral_unit hs, cpow_integral_unit hs']
      rw [show s + 1 + 1 = s + 2 by ring]
    _ = _ := by field_simp [h1, h2]; ring

private theorem riesz_integrand_eq_inner {s : ℂ} {x : ℝ} (hx : 0 < x) :
    (uncenteredRieszTwo x : ℂ) * (x : ℂ) ^ (-(s + 1)) =
      ∫ u in Ioc (0 : ℝ) 1, jointKernel s (x, u) := by
  have hcast :
      ((∫ u in Ioc (0 : ℝ) 1, (1 - u) * Chebyshev.psi (x * u) : ℝ) : ℂ) =
        ∫ u in Ioc (0 : ℝ) 1, (((1 - u) * Chebyshev.psi (x * u) : ℝ) : ℂ) :=
    integral_ofReal.symm
  calc
    _ = (2 : ℂ) *
        ((∫ u in Ioc (0 : ℝ) 1, (1 - u) * Chebyshev.psi (x * u) : ℝ) : ℂ) *
          (x : ℂ) ^ (-(s + 1)) := by
      rw [uncenteredRieszTwo_eq_convolution hx,
        intervalIntegral.integral_of_le zero_le_one]
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    _ = (2 : ℂ) *
        (∫ u in Ioc (0 : ℝ) 1, (((1 - u) * Chebyshev.psi (x * u) : ℝ) : ℂ)) *
          (x : ℂ) ^ (-(s + 1)) := by rw [hcast]
    _ = ∫ u in Ioc (0 : ℝ) 1,
        (2 : ℂ) * (((1 - u) * Chebyshev.psi (x * u) : ℝ) : ℂ) *
          (x : ℂ) ^ (-(s + 1)) := by
      rw [integral_mul_const, integral_const_mul]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only [jointKernel]
      push_cast
      ring

/-- The actual finite prime-power sum has a convergent Mellin integral for Re(s)>1. -/
theorem uncenteredRieszTwo_mellin_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (uncenteredRieszTwo x : ℂ) *
      (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  apply (jointKernel_integrable hs).integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (riesz_integrand_eq_inner (lt_trans zero_lt_one hx)).symm

/-- The actual arithmetic second-Riesz bridge, with no RH or spectral provider. -/
theorem uncenteredRieszTwo_mellin_psi {s : ℂ} (hs : 1 < s.re) :
    (∫ x in Ioi (1 : ℝ), (uncenteredRieszTwo x : ℂ) *
      (x : ℂ) ^ (-(s + 1))) =
      (2 / ((s + 1) * (s + 2))) *
        ∫ x in Ioi (1 : ℝ), (Chebyshev.psi x : ℂ) *
          (x : ℂ) ^ (-(s + 1)) := by
  calc
    _ = ∫ x in Ioi (1 : ℝ), ∫ u in Ioc (0 : ℝ) 1, jointKernel s (x, u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact riesz_integrand_eq_inner (lt_trans zero_lt_one hx)
    _ = ∫ u in Ioc (0 : ℝ) 1, ∫ x in Ioi (1 : ℝ), jointKernel s (x, u) :=
      integral_integral_swap (jointKernel_integrable hs)
    _ = ∫ u in Ioc (0 : ℝ) 1, (((2 * (1 - u) : ℝ) : ℂ) * (u : ℂ) ^ s) *
        (∫ x in Ioi (1 : ℝ), (Chebyshev.psi x : ℂ) *
          (x : ℂ) ^ (-(s + 1))) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only
      simp only [jointKernel, mul_assoc]
      rw [integral_const_mul, psi_scaled_mellin hu.1 hu.2]
    _ = _ := by rw [integral_mul_const, beta_moment (by linarith : -1 < s.re)]

/-- The proved convergent integral is the actual zeta logarithmic derivative. -/
theorem uncenteredRieszTwo_mellin_identity {s : ℂ} (hs : 1 < s.re) :
    (∫ x in Ioi (1 : ℝ), (uncenteredRieszTwo x : ℂ) *
      (x : ℂ) ^ (-(s + 1))) =
      -2 * deriv riemannZeta s /
        (s * (s + 1) * (s + 2) * riemannZeta s) := by
  rw [uncenteredRieszTwo_mellin_psi hs, psi_mellin_identity hs]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The actual centered Riesz vector also has a convergent integral on Re(s)>1. -/
theorem actualRieszTwo_mellin_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (AnnularZeroSpectral.actualRieszTwo x : ℂ) *
      (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hi := (uncenteredRieszTwo_mellin_integrable hs).sub
    ((linear_mellin_integrable hs).div_const (3 : ℂ))
  apply hi.congr_fun
  · intro x hx
    dsimp only [Pi.sub_apply, AnnularZeroSpectral.actualRieszTwo,
      AnnularPrimePair.indices, uncenteredRieszTwo]
    push_cast
    rw [show -s - 1 = -(s + 1) by ring]
    ring
  · exact measurableSet_Ioi

/-- Exact centering closes the original actual Riesz Mellin identity target. -/
theorem actualRieszTwo_mellin_identity {s : ℂ} (hs : 1 < s.re) :
    AnnularZeroSpectral.actualRieszTwoMellin s =
      -2 * logDeriv riemannZeta s / (s * (s + 1) * (s + 2)) -
        1 / (3 * (s - 1)) := by
  unfold AnnularZeroSpectral.actualRieszTwoMellin
  rw [show -s - 1 = -(s + 1) by ring]
  calc
    _ = ∫ x in Ioi (1 : ℝ),
        (uncenteredRieszTwo x : ℂ) * (x : ℂ) ^ (-(s + 1)) -
          ((x : ℂ) * (x : ℂ) ^ (-(s + 1))) / 3 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only [AnnularZeroSpectral.actualRieszTwo,
        AnnularPrimePair.indices, uncenteredRieszTwo]
      push_cast
      ring
    _ = (∫ x in Ioi (1 : ℝ), (uncenteredRieszTwo x : ℂ) *
        (x : ℂ) ^ (-(s + 1))) -
        (∫ x in Ioi (1 : ℝ), (x : ℂ) * (x : ℂ) ^ (-(s + 1))) / 3 := by
      have hsub := integral_sub (uncenteredRieszTwo_mellin_integrable hs)
        ((linear_mellin_integrable hs).div_const (3 : ℂ))
      rw [hsub, integral_div]
    _ = _ := by
      rw [uncenteredRieszTwo_mellin_identity hs, linear_mellin_integral hs,
        logDeriv_apply]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The named provider is supplied by the actual arithmetic integral proof. -/
theorem actualRieszMellinProvider : AnnularZeroSpectral.ActualRieszMellinProvider := by
  intro s hs
  exact actualRieszTwo_mellin_identity hs

end RiemannResearch.RH.ActualRieszTwo
