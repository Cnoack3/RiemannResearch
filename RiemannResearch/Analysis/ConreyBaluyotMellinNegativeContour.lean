/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotMellinContour
import RiemannResearch.RH.WeilExplicitFormula.RvM.ZetaGrowth
import RiemannResearch.Analysis.GammaMellinBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform negative-contour bounds for the Conrey--Baluyot weight

Source for the negative line and required uniformity: S. A. C. Baluyot,
*On the Zeros of Riemann's Zeta-function* (2017), Lemma 3.1.1,
equation (3.1.3), pp. 94--95:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The explicit constants are obtained from the Gamma recurrence and the proved
half-plane zeta estimate. Absolute convergence is proved before the actual
negative-line integral is bounded. The contour identity is in the sibling
shift module; no density or moment estimate is assumed here.
-/

open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

private theorem zeta_quarter_strip_bound {s : ℂ} (hlo : (1 / 4 : ℝ) ≤ s.re)
    (hhi : s.re ≤ 3 / 4) :
    ‖riemannZeta s‖ ≤ 8 + 4 * |s.im| := by
  have hp : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hhi
  have hd : 1 / 4 ≤ ‖1-s‖ := by
    have h := Complex.abs_re_le_norm (1-s)
    simp only [Complex.sub_re, Complex.one_re] at h
    rw [abs_of_nonneg (by linarith)] at h
    linarith
  have hdiv : 1 / ‖1-s‖ ≤ 4 := by
    apply (div_le_iff₀ (by linarith : 0 < ‖1-s‖)).mpr
    linarith
  have hs : ‖s‖ / s.re ≤ 1 + 4 * |s.im| := by
    have hn := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hp] at hn
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ 4*s.re-1) (abs_nonneg s.im)]
  have hh := Zeta23.RvM.norm_riemannZeta_le_of_re_pos hp hs1
  linarith
/-- Holomorphy on Re z > -1 away from the two possible zeta poles. -/
theorem differentiableAt_mellinKernel_off_poles {σ ξ : ℝ}
    (hξ : 0 < ξ) {z : ℂ} (hz : -1 < z.re)
    (hz0 : z ≠ 0) (hzp : z ≠ 1 - (2 * σ : ℝ)) :
    DifferentiableAt ℂ (mellinKernel σ ξ) z := by
  have hg : DifferentiableAt ℂ (fun w : ℂ => Gamma (w + 1)) z := by
    apply (Complex.differentiableAt_Gamma _ ?_).comp z
      (differentiableAt_id.add_const 1)
    intro n hn
    have he := congrArg Complex.re hn
    simp at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hl : DifferentiableAt ℂ (fun w : ℂ => riemannZeta ((2 * σ : ℝ) + w)) z := by
    apply (differentiableAt_riemannZeta ?_).comp z
      (differentiableAt_id.const_add _)
    intro he
    change (2 * σ : ℝ) + z = 1 at he
    apply hzp
    calc z = ((2 * σ : ℝ) + z) - (2 * σ : ℝ) := by ring
         _ = 1 - (2 * σ : ℝ) := by rw [he]
  have hr : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (1 + w)) z := by
    apply (differentiableAt_riemannZeta ?_).comp z
      (differentiableAt_id.const_add _)
    intro he
    apply hz0
    exact add_left_cancel (by simpa using he : (1 : ℂ) + z = 1 + 0)
  have hp : DifferentiableAt ℂ (fun w : ℂ => (ξ : ℂ) ^ w) z := by
    have hne : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
    simp only [Complex.cpow_def_of_ne_zero hne]
    fun_prop
  exact ((hg.mul (hl.div_const _)).mul hr).mul hp

/-- Explicit negative-line majorant, with a constant independent of sigma and xi. -/
theorem norm_mellinIntegrand_negative_le {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hσhi : σ ≤ 3 / 4) (hξ : 0 < ξ) (t : ℝ) :
    ‖mellinIntegrand σ ξ (-(3 / 4)) t‖ ≤
      (2048 * Real.Gamma (17 / 4) * ξ ^ (-(3 / 4 : ℝ))) * (1 + t ^ 2)⁻¹ := by
  let z : ℂ := (-(3 / 4 : ℝ) : ℂ) + I * t
  have hg : ‖Gamma (z + 1)‖ ≤
      16 * Real.Gamma (17 / 4) / (1 + t ^ 2) ^ 2 := by
    simpa [z, show -(3 / 4 : ℝ) + 5 = 17 / 4 by norm_num] using
      Complex.gamma_vertical_quartic_bound (r := -(3 / 4)) le_rfl t
  have hl : ‖riemannZeta ((2 * σ : ℝ) + z)‖ ≤ 8 + 4 * |t| := by
    simpa [z] using
      zeta_quarter_strip_bound (s := (2 * σ : ℝ) + z)
        (by simp [z]; linarith) (by simp [z]; linarith)
  have hr : ‖riemannZeta (1 + z)‖ ≤ 8 + 4 * |t| := by
    simpa [z] using zeta_quarter_strip_bound (s := 1 + z)
      (by norm_num [z]) (by norm_num [z])
  have hd : 1 ≤ ‖riemannZeta (2 * σ : ℝ)‖ :=
    one_le_norm_riemannZeta_real (by linarith)
  have hq : ‖riemannZeta ((2 * σ : ℝ) + z) / riemannZeta (2 * σ : ℝ)‖ ≤
      ‖riemannZeta ((2 * σ : ℝ) + z)‖ := by
    rw [norm_div]
    exact div_le_self (norm_nonneg _) hd
  have hprod :
      ‖riemannZeta ((2 * σ : ℝ) + z) / riemannZeta (2 * σ : ℝ)‖ *
      ‖riemannZeta (1 + z)‖ ≤ 128 * (1 + t ^ 2) := by
    calc
      _ ≤ (8 + 4 * |t|) * (8 + 4 * |t|) :=
        mul_le_mul (hq.trans hl) hr (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith only [sq_abs t, sq_nonneg (|t| - 2)]
  have hp : ‖(ξ : ℂ) ^ z‖ = ξ ^ (-(3 / 4 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hξ]
    simp [z]
  have hD : 0 < 1 + t ^ 2 := by positivity
  dsimp only [mellinIntegrand]
  simp only [Complex.ofReal_neg]
  change ‖Gamma (z + 1) * _ * _ * _‖ ≤ _
  simp only [norm_mul]
  rw [hp, mul_assoc ‖Gamma (z+1)‖]
  calc
    _ ≤ (16 * Real.Gamma (17 / 4) / (1 + t ^ 2) ^ 2) *
        (128 * (1 + t ^ 2)) * ξ ^ (-(3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hg hprod (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (by positivity)) (Real.rpow_nonneg hξ.le _)
    _ = _ := by field_simp [ne_of_gt hD]; ring

/-- Absolute convergence of the actual negative-contour integral. -/
theorem integrable_mellinIntegrand_negative {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hσhi : σ ≤ 3 / 4) (hξ : 0 < ξ) :
    Integrable (mellinIntegrand σ ξ (-(3 / 4))) := by
  have hc : Continuous (mellinIntegrand σ ξ (-(3 / 4))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hd := differentiableAt_mellinKernel_off_poles (σ := σ) hξ
      (z := (-(3 / 4 : ℝ) : ℂ) + t * I) (by norm_num)
      (by intro h; have := congrArg Complex.re h; norm_num at this)
      (by intro h; have := congrArg Complex.re h; simp at this; linarith)
    have hh : ContinuousAt
        (fun u : ℝ => mellinKernel σ ξ ((-(3 / 4 : ℝ) : ℂ) + u * I)) t :=
      ContinuousAt.comp (f := fun u : ℝ => (-(3 / 4 : ℝ) : ℂ) + u * I)
        hd.continuousAt (by fun_prop)
    convert hh using 1
    funext u
    simpa only [Complex.ofReal_neg] using (mellinKernel_onLine σ ξ (-(3 / 4)) u).symm
  apply (integrable_inv_one_add_sq.const_mul
    (2048 * Real.Gamma (17 / 4) * ξ ^ (-(3 / 4 : ℝ)))).mono'
    hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_mellinIntegrand_negative_le hσ hσhi hξ)

/-- Uniform remainder estimate for the actual line Re z = -3 / 4. -/
theorem norm_weightOnLine_negative_le {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hσhi : σ ≤ 3 / 4) (hξ : 0 < ξ) :
    ‖weightOnLine σ ξ (-(3 / 4))‖ ≤
      1024 * Real.Gamma (17 / 4) * ξ ^ (-(3 / 4 : ℝ)) := by
  have hI := integrable_mellinIntegrand_negative hσ hσhi hξ
  have hbound : ‖∫ t : ℝ, mellinIntegrand σ ξ (-(3 / 4)) t‖ ≤
      (2048 * Real.Gamma (17 / 4) * ξ ^ (-(3 / 4 : ℝ))) * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, ‖mellinIntegrand σ ξ (-(3 / 4)) t‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (2048 * Real.Gamma (17 / 4) * ξ ^ (-(3 / 4 : ℝ))) *
          (1 + t ^ 2)⁻¹ :=
        integral_mono hI.norm (integrable_inv_one_add_sq.const_mul _)
          (norm_mellinIntegrand_negative_le hσ hσhi hξ)
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  unfold weightOnLine
  rw [norm_mul, norm_inv]
  have hnorm : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      Complex.norm_of_nonneg (by positivity)]
  rw [hnorm]
  calc
    _ ≤ (2 * Real.pi)⁻¹ *
        ((2048 * Real.Gamma (17 / 4) * ξ ^ (-(3 / 4 : ℝ))) * Real.pi) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero]; ring

end RiemannResearch.Analysis.ConreyBaluyot
