/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreePolarizedMellin
import RiemannResearch.RH.PrimeTreeExpSubstitution
import RiemannResearch.Analysis.FourierL1L2Plancherel
import Mathlib.Analysis.MellinInversion
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The polarized critical line identity
Angular-frequency Fourier–Plancherel for the full positive Mellin ray, followed
by the complex finite-packet specialization of Section 6.1, equation (26). -/

noncomputable section
open Set MeasureTheory Filter
open scoped FourierTransform Real Topology BigOperators
namespace RiemannResearch.RH.PrimeTreeScalingEnergy
open RiemannResearch.Analysis ZetaTwoProbability

theorem critical_mellin_plancherel (f : ℝ → ℂ)
    (h₁ : MellinConvergent f (-(1 / 2 : ℂ)))
    (h₂ : IntegrableOn (fun x : ℝ => ‖f x / (x : ℂ)‖ ^ 2) (Ioi 0)) :
    (∫ t : ℝ, ‖mellin f (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2) =
      (2 * Real.pi) * ∫ x in Ioi (0 : ℝ), ‖f x / (x : ℂ)‖ ^ 2 := by
  let g (u : ℝ) : ℂ := Real.exp (1 / 2 * u) • f (Real.exp (-u))
  let E (x : ℝ) : ℝ := ‖f x / (x : ℂ)‖ ^ 2
  have hL₁ : Integrable g := by
    let H (x : ℝ) := (x : ℂ) ^ (-(1 / 2 : ℂ) - 1) • f x
    have hi := ((integrable_comp_exp_full H).mpr h₁).comp_neg
    apply hi.congr
    filter_upwards with u
    have hfac : (Real.exp (-u) : ℂ) * (Real.exp (-u) : ℂ) ^ (-(1 / 2 : ℂ) - 1) =
        (Real.exp (1 / 2 * u) : ℂ) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
        ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp,
        Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    dsimp only [g, H]
    simp only [Complex.real_smul, smul_eq_mul, ← mul_assoc, hfac]
  have hsq (u : ℝ) : ‖g u‖ ^ 2 = Real.exp (-u) * E (Real.exp (-u)) := by
    have hfac : Real.exp (1 / 2 * u) ^ 2 = (Real.exp (-u))⁻¹ := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_neg]
      congr 1
      ring
    dsimp only [g, E]
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, hfac, norm_div,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    field_simp [ne_of_gt (Real.exp_pos (-u))]
  have hi₂ := (integrable_comp_exp_full E).mpr h₂
  have hg2 : MemLp g 2 := (memLp_two_iff_integrable_sq_norm hL₁.aestronglyMeasurable).mpr
    (by simpa only [hsq, smul_eq_mul] using hi₂.comp_neg)
  have hFourier := integral_norm_sq_fourier_of_integrable hL₁ hg2
  have hM (t : ℝ) :
      mellin f (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) = 𝓕 g (-t / (2 * Real.pi)) := by
    rw [mellin_eq_fourier]
    simp [g]
  have hE : (∫ u, ‖g u‖ ^ 2) = ∫ x in Ioi (0 : ℝ), E x := by
    simp_rw [hsq]
    calc
      _ = ∫ u : ℝ, Real.exp u * E (Real.exp u) :=
        integral_neg_eq_self (fun u : ℝ => Real.exp u * E (Real.exp u)) volume
      _ = _ := integral_comp_exp_full E
  rw [hE] at hFourier
  let F (t : ℝ) := ‖𝓕 g t‖ ^ 2
  let a : ℝ := 2 * Real.pi
  have ha : 0 < a := by dsimp [a]; positivity
  have hscale := Measure.integral_comp_mul_left F (-a⁻¹)
  have hfac : |(-a⁻¹)⁻¹| = a := by rw [inv_neg, inv_inv, abs_neg, abs_of_pos ha]
  rw [hfac, smul_eq_mul] at hscale
  change _ = (2 * Real.pi) * ∫ x in Ioi (0 : ℝ), E x
  rw [← hFourier]
  calc
    _ = ∫ t : ℝ, F (-a⁻¹ * t) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hM]
      change ‖𝓕 g _‖ ^ 2 = ‖𝓕 g _‖ ^ 2
      rw [show -a⁻¹ * t = -t / (2 * Real.pi) by dsimp [a]; ring]
    _ = _ := hscale

/-- Equation (26) for arbitrary fixed finite vectors of complex coefficients. -/
theorem tendsto_packetQEnergy_critical {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (ha : ∀ j, 0 < a j) (v : ι → ℂ) :
    Tendsto (fun D : ℕ => (D : ℝ) * packetQEnergy D a v) atTop
      (𝓝 ((1 / (2 * Real.pi * zetaTwo)) *
        ∫ t : ℝ, ‖(riemannZeta ((1 / 2 : ℂ) + t * Complex.I) /
          ((1 / 2 : ℂ) + t * Complex.I)) *
          ∑ j, v j * (a j : ℂ) ^ (-((1 / 2 : ℂ) + t * Complex.I))‖ ^ 2)) := by
  have hp := critical_mellin_plancherel (packet a v)
    (packet_mellin_convergent a ha v _ (by norm_num) (by norm_num))
    (packetProfile_integrable_sq a ha v)
  have h (t : ℝ) : ‖mellin (packet a v) (-((1 / 2 : ℂ) + t * Complex.I))‖ =
      ‖(riemannZeta ((1 / 2 : ℂ) + t * Complex.I) / ((1 / 2 : ℂ) + t * Complex.I)) *
        ∑ j, v j * (a j : ℂ) ^ (-((1 / 2 : ℂ) + t * Complex.I))‖ := by
    rw [mellin_packet a ha v _ (by norm_num) (by norm_num), neg_div, neg_mul, norm_neg]
  simp_rw [h] at hp
  have hcancel (x : ℝ) : (1 / (2 * Real.pi * zetaTwo)) * ((2 * Real.pi) * x) =
      x / zetaTwo := by field_simp [Real.pi_ne_zero, zetaTwo_pos.ne']
  rw [hp, hcancel]
  exact tendsto_packetQEnergy a ha v

end RiemannResearch.RH.PrimeTreeScalingEnergy
