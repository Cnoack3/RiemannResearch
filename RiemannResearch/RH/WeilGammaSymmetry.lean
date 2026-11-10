/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.WeilGammaFourierAdapter
import RiemannResearch.RH.WeilExplicitFormula.WeilEF.GammaRBracket
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Gamma symmetry and shifted real tests

The compact-C2 gamma functional is linear and reflection invariant. It is
real for every real spatial test, including a shifted test. Symmetrization
then supplies the complete regulated formula without an evenness hypothesis
on the original test; positive support removes the reflected term exactly.

Source: the repository's checked gamma adapter and the digamma conjugation
identity in Guinand--Weil, with the representation in DLMF5.9.16,
https://dlmf.nist.gov/5.9.E16. The additional symmetry transport is proved here
from exact Fourier identities; no zeta-zero distribution assumption is used.
-/
open MeasureTheory Set Complex
open scoped FourierTransform
noncomputable section
namespace RiemannResearch.RH.SignedWeilCorrelation
open Zeta23

def gammaFunctional (k : ℝ → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ)

theorem paperFT_const_mul (k : ℝ → ℂ) (a z : ℂ) :
    paperFT (fun t => a * k t) z = a * paperFT k z := by
  simp only [paperFT, mul_assoc, integral_const_mul]

theorem gammaFunctional_const_mul (k : ℝ → ℂ) (a : ℂ) :
    gammaFunctional (fun t => a * k t) = a * gammaFunctional k := by
  simp only [gammaFunctional, paperFT_const_mul, mul_assoc, integral_const_mul]
  ring

theorem gammaFunctional_im_eq_zero {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hc : HasCompactSupport k)
    (hr : ∀ t, (k t).im = 0) : (gammaFunctional k).im = 0 := by
  have h := gamma_spatial_of_contDiff_two (contDiff_const.mul hk)
    (show HasCompactSupport (fun t : ℝ => Complex.I * k t) from hc.mul_left)
    (show ∀ t, (Complex.I * k (-t)).re = (Complex.I * k t).re by simp [hr])
  change (gammaFunctional (fun t => Complex.I * k t)).re = _ at h
  rw [gammaFunctional_const_mul] at h
  simpa [hr] using h

theorem gammaBracket_neg (r : ℝ) : EF.gammaBracket (-r) = EF.gammaBracket r := by
  have h (t : ℝ) :
      logDeriv Complex.Gammaℝ (1/2 + t * I) +
        logDeriv Complex.Gammaℝ (1/2 - t * I) = (EF.gammaBracket t : ℂ) := by
    have ha : (1 / 4 : ℂ) + (t : ℂ) / 2 * I =
        (1 / 4 : ℂ) + I * (t : ℂ) / 2 := by ring
    simpa only [EF.gammaBracket, ha] using Zeta23.WeilEF.gammaR_bracket t
  apply Complex.ofReal_injective
  rw [← h (-r), ← h r]
  push_cast
  rw [show (1/2:ℂ) + -(r:ℂ) * I = 1/2 - r * I by ring,
    show (1/2:ℂ) - -(r:ℂ) * I = 1/2 + r * I by ring]
  exact add_comm _ _

theorem paperFT_reflect (k : ℝ → ℂ) (z : ℂ) :
    paperFT (fun t => k (-t)) z = paperFT k (-z) := by
  unfold paperFT
  calc
    (∫ t : ℝ, k (-t) * cexp (I * z * t)) =
      ∫ t : ℝ, k (-t) * cexp (I * (-z) * (-t : ℝ)) := by
        congr 1
        funext t
        push_cast
        congr 2
        ring
    _ = _ := integral_neg_eq_self (fun t : ℝ => k t * cexp (I * (-z) * (t : ℂ))) volume

theorem gammaFunctional_reflect (k : ℝ → ℂ) :
    gammaFunctional (fun t => k (-t)) = gammaFunctional k := by
  unfold gammaFunctional
  congr 1
  simp_rw [paperFT_reflect]
  calc
    (∫ r : ℝ, paperFT k (-↑r) * ↑(EF.gammaBracket r)) =
      ∫ r : ℝ, paperFT k ↑(-r) * ↑(EF.gammaBracket (-r)) := by
        simp only [Complex.ofReal_neg, gammaBracket_neg]
    _ = _ := integral_neg_eq_self (fun r : ℝ => paperFT k (r : ℂ) * (EF.gammaBracket r : ℂ)) volume

theorem integrable_gammaFunctional_integrand {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hc : HasCompactSupport k) :
    Integrable (fun r : ℝ => paperFT k r * (EF.gammaBracket r : ℂ)) := by
  have hi : Integrable k := hk.continuous.integrable_of_hasCompactSupport hc
  have hfi := EF.integrable_fourier_of_contDiff_two hk hc
  have hHc : Continuous (fun r : ℝ => paperFT k r) := by
    simp_rw [EF.paperFT_ofReal_eq_fourier]
    exact (EF.continuous_fourier_of_integrable hi).comp (by fun_prop)
  obtain ⟨L,hL⟩ := EF.exists_abs_le_of_hasCompactSupport hc
  let A : ℝ := (∫ u : ℝ, ‖k u‖) + ∫ u : ℝ, ‖deriv (deriv k) u‖
  have hA : 0 ≤ A := add_nonneg (integral_nonneg (fun _ => norm_nonneg _))
    (integral_nonneg (fun _ => norm_nonneg _))
  have hdec (r : ℝ) : ‖paperFT k r‖ ≤ A / (1+r^2) :=
    (le_div_iff₀ (by positivity)).mpr (EF.norm_paperFT_mul_one_add_sq_le hk hL r)
  have hI := integrable_mul_digammaIncrement_of_decay
    (fun r : ℝ => paperFT k r) hHc (EF.integrable_paperFT_ofReal hfi) A hA hdec
  let q : ℝ := (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi
  have he : (fun r : ℝ => paperFT k r * (EF.gammaBracket r : ℂ)) =
      fun r : ℝ => paperFT k r * (digammaIncrement r : ℂ) + paperFT k r * (q : ℂ) := by
    funext r
    have hb : EF.gammaBracket r = digammaIncrement r + q := by
      have ha : (1 / 4 : ℂ) + Complex.I * (r : ℂ) / 2 =
          (1 / 4 : ℂ) + Complex.I * (r / 2 : ℝ) := by push_cast; ring
      unfold EF.gammaBracket digammaIncrement q
      rw [ha]
      ring
    rw [hb]
    push_cast
    ring
  rw [he]
  exact hI.add ((EF.integrable_paperFT_ofReal hfi).mul_const _)

theorem paperFT_add_compact {k l : ℝ → ℂ}
    (hk : Continuous k) (hl : Continuous l)
    (hc : HasCompactSupport k) (hd : HasCompactSupport l) (z : ℂ) :
    paperFT (fun t => k t + l t) z = paperFT k z + paperFT l z := by
  unfold paperFT
  simp_rw [add_mul]
  apply integral_add
  · exact (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  · exact (hl.mul (by fun_prop)).integrable_of_hasCompactSupport hd.mul_right

theorem gammaFunctional_add {k l : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hl : ContDiff ℝ 2 l)
    (hc : HasCompactSupport k) (hd : HasCompactSupport l) :
    gammaFunctional (fun t => k t + l t) = gammaFunctional k + gammaFunctional l := by
  unfold gammaFunctional
  simp_rw [paperFT_add_compact hk.continuous hl.continuous hc hd, add_mul]
  rw [integral_add (integrable_gammaFunctional_integrand hk hc)
    (integrable_gammaFunctional_integrand hl hd)]
  ring

theorem gammaFunctional_real_spatial {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hc : HasCompactSupport k) (hr : ∀ t, (k t).im = 0) :
    gammaFunctional k =
      (-(Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) * (k 0).re -
        ∫ t, weilGammaKernel t *
          ((k t).re + (k (-t)).re - 2 * weilRegulator t * (k 0).re)
          ∂positiveMeasure : ℝ) := by
  have hk' : ContDiff ℝ 2 (fun t : ℝ => k (-t)) := hk.comp (by fun_prop)
  have hc' : HasCompactSupport (fun t : ℝ => k (-t)) :=
    hc.comp_homeomorph (Homeomorph.neg ℝ)
  have h := gamma_spatial_of_contDiff_two (hk.add hk') (hc.add hc')
    (show ∀ t : ℝ, (k (-t) + k (-(-t))).re = (k t + k (-t)).re by
      intro t; simp [add_comm])
  change (gammaFunctional (fun t => k t + k (-t))).re = _ at h
  rw [gammaFunctional_add hk hk' hc hc', gammaFunctional_reflect] at h
  simp only [Complex.add_re, neg_zero] at h
  have hf : (fun t => weilGammaKernel t *
      ((k t).re + (k (-t)).re - weilRegulator t * ((k 0).re + (k 0).re))) =
      (fun t => weilGammaKernel t *
      ((k t).re + (k (-t)).re - 2 * weilRegulator t * (k 0).re)) := by
    funext t; ring
  rw [hf] at h
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    linarith
  · simp only [Complex.ofReal_im]
    exact gammaFunctional_im_eq_zero hk hc hr
end RiemannResearch.RH.SignedWeilCorrelation

namespace RiemannResearch.RH.SignedWeilCorrelation
open Zeta23
theorem gammaFunctional_of_positive_support {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hc : HasCompactSupport k) (hr : ∀ t, (k t).im = 0)
    (hz : ∀ t : ℝ, t ≤ 0 → k t = 0) :
    gammaFunctional k = (-(∫ t : ℝ, weilGammaKernel t * (k t).re) : ℝ) := by
  rw [gammaFunctional_real_spatial hk hc hr, hz 0 le_rfl]
  simp only [Complex.zero_re, mul_zero, zero_sub]
  have hhalf : (∫ t, weilGammaKernel t * ((k t).re + (k (-t)).re - 0)
        ∂positiveMeasure) =
      ∫ t, weilGammaKernel t * (k t).re ∂positiveMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hz (-t) (by linarith [show 0 < t from ht])]
    simp
  rw [hhalf]
  have hind : (Ioi (0 : ℝ)).indicator (fun t => weilGammaKernel t * (k t).re) =
      (fun t => weilGammaKernel t * (k t).re) := by
    funext t
    by_cases ht : 0 < t
    · simp [ht]
    · simp [ht, hz t (le_of_not_gt ht)]
  have he := integral_indicator (μ := (volume : Measure ℝ)) (s := Ioi (0 : ℝ))
    (f := fun t => weilGammaKernel t * (k t).re) measurableSet_Ioi
  rw [hind] at he
  rw [show (∫ t, weilGammaKernel t * (k t).re ∂positiveMeasure) =
      ∫ t, weilGammaKernel t * (k t).re from he.symm]
end RiemannResearch.RH.SignedWeilCorrelation
