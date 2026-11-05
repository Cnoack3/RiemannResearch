/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeExpSubstitution
import RiemannResearch.RH.PrimeTreeFractionalMellin
import RiemannResearch.RH.PrimeTreeProbabilityMixture
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Fourier transforms of the two log laws
The Fourier sign is the minus sign in (15)–(16). The transform of the limiting
probability law is Nakamura's modified zeta characteristic function with
this sign convention. -/
noncomputable section
open Set MeasureTheory
namespace RiemannResearch.RH.PrimeTreeMellinLaws

def lawFourier (ν : Measure ℝ) (γ : ℝ) : ℂ :=
  ∫ t, Complex.exp (-((γ : ℂ) * t) * Complex.I) ∂ν

private theorem mellin_log_integral (f : ℝ → ℂ) (s : ℂ) :
    mellin f (-s) = ∫ t : ℝ, Complex.exp (-s * (t : ℂ)) * f (Real.exp t) := by
  rw [mellin, ← RiemannResearch.Analysis.integral_comp_exp_full]
  apply integral_congr_ae
  filter_upwards with t
  have he : (((Real.exp t : ℝ) : ℂ)) ^ (-s - 1) = Complex.exp ((t : ℂ) * (-s - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
      ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
  rw [Complex.real_smul, smul_eq_mul, he, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

private theorem mellin_log_mass (f : ℝ → ℝ) (σ : ℝ) :
    mellin (fun x : ℝ => ((f x : ℝ) : ℂ)) (-(σ : ℂ)) =
      ((∫ t : ℝ, f (Real.exp t) * Real.exp (-σ * t) : ℝ) : ℂ) := by
  rw [mellin_log_integral, ← integral_complex_ofReal (μ := volume)
    (f := fun t : ℝ => f (Real.exp t) * Real.exp (-σ * t))]
  apply integral_congr_ae
  filter_upwards with t
  push_cast
  ring

/-- Fourier normalization as a ratio of two actual Mellin integrals. -/
theorem lawFourier_mellin_ratio (f : ℝ → ℝ) (hm : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (σ γ : ℝ) :
    lawFourier (normalizedLaw (fun t => f (Real.exp t) * Real.exp (-σ * t))) γ =
      mellin (fun x : ℝ => ((f x : ℝ) : ℂ)) (-((σ : ℂ) + (γ : ℂ) * Complex.I)) /
      mellin (fun x : ℝ => ((f x : ℝ) : ℂ)) (-(σ : ℂ)) := by
  let w (t : ℝ) := f (Real.exp t) * Real.exp (-σ * t)
  have hw : Measurable w := (hm.comp Real.measurable_exp).mul (by fun_prop)
  have hnn (t : ℝ) : 0 ≤ w t := mul_nonneg (hn _) (Real.exp_pos _).le
  have hi : 0 ≤ ∫ t, w t := integral_nonneg hnn
  change (∫ t, Complex.exp (-((γ : ℂ) * t) * Complex.I) ∂(normalizedLaw w)) = _
  have hden : Measurable (fun t : ℝ => ENNReal.ofReal (w t / ∫ u, w u)) :=
    ENNReal.measurable_ofReal.comp (hw.div_const _)
  rw [normalizedLaw, integral_withDensity_eq_integral_toReal_smul
    (μ := (volume : Measure ℝ)) hden
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _, mellin_log_mass,
    mellin_log_integral, ← integral_div]
  apply integral_congr_ae
  filter_upwards with t
  rw [ENNReal.toReal_ofReal (div_nonneg (hnn t) hi), Complex.real_smul]
  dsimp only [w]
  push_cast
  have harg : -((σ : ℂ) + γ * Complex.I) * t =
      -((σ : ℂ) * t) + (-((γ : ℂ) * t) * Complex.I) := by ring
  rw [harg, Complex.exp_add]
  ring

theorem limitLaw_fourier (σ γ : ℝ) (hσ : 0 < σ) (hσ' : σ < 1) :
    lawFourier (normalizedLaw (logWeight σ)) γ =
      (-(riemannZeta ((σ : ℂ) + γ * Complex.I)) / ((σ : ℂ) + γ * Complex.I)) /
        (-riemannZeta (σ : ℂ) / (σ : ℂ)) := by
  change lawFourier (normalizedLaw (fun t => Int.fract (Real.exp t) * Real.exp (-σ * t))) γ = _
  rw [lawFourier_mellin_ratio Int.fract measurable_fract Int.fract_nonneg]
  rw [mellin_fract_zeta, mellin_fract_zeta] <;> first | simpa using hσ | simpa using hσ'

theorem limitLaw_fourier_zero_iff (σ γ : ℝ) (hσ : 0 < σ) (hσ' : σ < 1) :
    lawFourier (normalizedLaw (logWeight σ)) γ = 0 ↔
      riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I) = 0 := by
  have hc : (((∫ t, logWeight σ t : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (integral_logWeight_pos σ hσ hσ').ne'
  have hs : (σ : ℂ) + (γ : ℂ) * Complex.I ≠ 0 := by
    intro e
    have hr := congrArg Complex.re e
    simp at hr
    linarith
  change lawFourier (normalizedLaw (fun t => Int.fract (Real.exp t) * Real.exp (-σ * t))) γ = 0 ↔ _
  rw [lawFourier_mellin_ratio Int.fract measurable_fract Int.fract_nonneg, mellin_log_mass,
    mellin_fract_zeta _ (by simpa using hσ) (by simpa using hσ')]
  change (_ / _) / (((∫ t, logWeight σ t : ℝ)) : ℂ) = 0 ↔ _
  rw [div_eq_zero_iff, or_iff_left hc, div_eq_zero_iff, or_iff_left hs, neg_eq_zero]

private theorem staircase_measurable (D : ℕ) : Measurable (staircase D) :=
  (measurable_of_countable (Pareto.normalizedAtom D)).comp
    (Nat.measurable_floor.comp (measurable_const.mul measurable_id))

theorem depthLaw_fourier (D : ℕ) (hD : 0 < D) (σ γ : ℝ) (hσ : 0 < σ) (hσ' : σ < 1) :
    lawFourier (normalizedLaw (logDepthWeight D σ)) γ =
      ((1 - (D : ℂ) ^ ((σ : ℂ) + γ * Complex.I - 1)) *
        (-riemannZeta ((σ : ℂ) + γ * Complex.I) / ((σ : ℂ) + γ * Complex.I))) /
      ((1 - (D : ℂ) ^ ((σ : ℂ) - 1)) * (-riemannZeta (σ : ℂ) / (σ : ℂ))) := by
  change lawFourier (normalizedLaw (fun t => staircase D (Real.exp t) * Real.exp (-σ * t))) γ = _
  rw [lawFourier_mellin_ratio _ (staircase_measurable D) (staircase_nonneg D),
    mellin_staircase_zeta, mellin_staircase_zeta]
  all_goals first | exact hD | simpa using hσ | intro e; have e' := congrArg Complex.re e; simp at e'; linarith

theorem depthLaw_fourier_zero_iff (D : ℕ) (hD : 1 < D) (σ γ : ℝ)
    (hσ : 0 < σ) (hσ' : σ < 1) :
    lawFourier (normalizedLaw (logDepthWeight D σ)) γ = 0 ↔
      riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I) = 0 := by
  have hm := integral_logDepthWeight D (by omega) σ hσ hσ'
  have hd : (1 : ℝ) < D := by exact_mod_cast hD
  have hδ : missingMass D σ < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hd (sub_neg.mpr hσ')
  have hnorm : (0 : ℝ) < ∫ t, logDepthWeight D σ t := by
    rw [hm]
    exact mul_pos (sub_pos.mpr hδ) (integral_logWeight_pos σ hσ hσ')
  change lawFourier (normalizedLaw (fun t => staircase D (Real.exp t) * Real.exp (-σ * t))) γ = 0 ↔ _
  rw [lawFourier_mellin_ratio _ (staircase_measurable D) (staircase_nonneg D),
    mellin_log_mass]
  have hc : (((∫ t, logDepthWeight D σ t : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm.ne'
  change _ / (((∫ t, logDepthWeight D σ t : ℝ)) : ℂ) = 0 ↔ _
  rw [div_eq_zero_iff, or_iff_left hc]
  exact mellin_staircase_zero_iff D hD _ (by simpa using hσ) (by simpa using hσ'.ne)

theorem riemannHypothesis_iff_depthLaw_zero_free (D : ℕ) (hD : 1 < D) :
    RiemannHypothesis ↔ ∀ σ γ : ℝ, 1 / 2 < σ → σ < 1 →
      lawFourier (normalizedLaw (logDepthWeight D σ)) γ ≠ 0 := by
  rw [riemannHypothesis_iff_right_half_strip_zero_free]
  constructor
  · intro h σ γ hhalf hlt hz
    apply h ((σ : ℂ) + (γ : ℂ) * Complex.I) (by simpa using hhalf) (by simpa using hlt)
    exact (depthLaw_fourier_zero_iff D hD σ γ (by linarith) hlt).mp hz
  · intro h s hhalf hlt hz
    apply h s.re s.im hhalf hlt
    apply (depthLaw_fourier_zero_iff D hD _ _ (by linarith) hlt).mpr
    simpa only [Complex.re_add_im] using hz

end RiemannResearch.RH.PrimeTreeMellinLaws
