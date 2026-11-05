/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeScalingEnergy
import RiemannResearch.RH.PrimeTreeFractionalMellin
import RiemannResearch.RH.PrimeTreeProbabilityMixture
import RiemannResearch.RH.PrimeTreeExpSubstitution
import RiemannResearch.Analysis.FourierL1L2Plancherel
import Mathlib.Analysis.MellinInversion
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Critical-line zeta energy
This is the Parseval argument in Section 6.1 of the prime-tree paper. The
exact zeta second moment is also discussed by M. W. Coffey, arXiv:1101.5722. -/
noncomputable section
open Set MeasureTheory Filter
open scoped FourierTransform Real Topology
namespace RiemannResearch.RH.PrimeTreeScalingEnergy
open RiemannResearch.Analysis PrimeTreeMellinLaws ZetaTwoHilbert ZetaTwoProbability

/-- The half-line datum in Mathlib's Mellin–Fourier convention uses −u. -/
private def g (u : ℝ) : ℂ := ((logWeight (1/2) (-u) : ℝ) : ℂ)

private def energy (x : ℝ) : ℝ := (Int.fract x) ^ 2 / x ^ 2

private theorem g_energy (u : ℝ) :
    ‖g u‖ ^ 2 = Real.exp (-u) * energy (Real.exp (-u)) := by
  have hsq : Real.exp (-(1 / 2 : ℝ) * (-u)) ^ 2 = (Real.exp (-u))⁻¹ := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  rw [g, Complex.norm_real, Real.norm_eq_abs, sq_abs, logWeight, mul_pow, hsq, energy]
  field_simp [ne_of_gt (Real.exp_pos (-u))]

private theorem g_fourier (t : ℝ) :
    𝓕 g (-t / (2 * Real.pi)) =
      -riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) /
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
  let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have hre : s.re = 1 / 2 := by simp [s]
  have him : s.im = t := by simp [s]
  have hm := mellin_fract_zeta s (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  rw [mellin_eq_fourier] at hm
  have hfn : (fun u : ℝ => Real.exp (-(-s).re * u) • ((Int.fract (Real.exp (-u)) : ℝ) : ℂ)) =
      g := by
    funext u
    simp only [Complex.neg_re, neg_neg, hre, g, logWeight, Complex.ofReal_mul, Complex.real_smul]
    rw [show -(1 / 2 : ℝ) * (-u) = 1 / 2 * u by ring]
    ring
  rw [hfn, Complex.neg_im, him] at hm
  exact hm

/-- The unscaled exact continuum identity behind equation (25). -/
theorem critical_integral :
    (∫ t : ℝ, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) /
      ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) =
      (2 * Real.pi) * (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) := by
  have hg : Integrable g :=
    (integrable_logWeight (1/2) (by norm_num) (by norm_num)).comp_neg.ofReal
  have hE : IntegrableOn energy (Ioi 0) := StepCorrectionNorm.fract_energy_integrable
  have hi := (integrable_comp_exp_full energy).mpr hE
  have hg2 : MemLp g 2 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr
    (by simpa only [g_energy, smul_eq_mul] using hi.comp_neg)
  have hp := integral_norm_sq_fourier_of_integrable hg hg2
  have he : (∫ u, ‖g u‖ ^ 2) =
      Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
    simp_rw [g_energy]
    calc
      _ = ∫ u : ℝ, Real.exp u * energy (Real.exp u) :=
        integral_neg_eq_self (fun u : ℝ => Real.exp u * energy (Real.exp u)) volume
      _ = ∫ x in Ioi (0 : ℝ), energy x := integral_comp_exp_full energy
      _ = _ := StepCorrectionNorm.fract_energy_eq_log_two_pi_sub_gamma
  rw [he] at hp
  let F (t : ℝ) := ‖𝓕 g t‖ ^ 2
  let a : ℝ := (2 * Real.pi)
  have ha : 0 < a := by dsimp [a]; positivity
  have hscale := Measure.integral_comp_mul_left F (-a⁻¹)
  have hfac : |(-a⁻¹)⁻¹| = a := by rw [inv_neg, inv_inv, abs_neg, abs_of_pos ha]
  rw [hfac, smul_eq_mul] at hscale
  rw [← hp]
  calc
    _ = ∫ t : ℝ, F (-a⁻¹ * t) := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [F]
      rw [show -a⁻¹ * t = -t / (2 * Real.pi) by dsimp [a]; ring, g_fourier,
        neg_div, norm_neg]
    _ = _ := hscale

/-- The tree's full discrete energy expressed as an angular-frequency zeta integral. -/
theorem tendsto_conductor_energy_critical :
    Tendsto (fun D : ℕ => (D : ℝ) * ‖qResidue D‖ ^ 2) atTop
      (𝓝 ((1 / (2 * Real.pi * zetaTwo)) *
        ∫ t : ℝ, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) /
          ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)) := by
  rw [critical_integral]
  convert tendsto_conductor_energy using 2 <;> field_simp [Real.pi_ne_zero, zetaTwo_pos.ne'] <;> ring

end RiemannResearch.RH.PrimeTreeScalingEnergy
