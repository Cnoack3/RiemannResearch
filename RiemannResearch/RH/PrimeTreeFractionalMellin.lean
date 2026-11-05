/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeMellinLaws
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.MellinTransform

/-! # The full fractional-part Mellin integral and the exact conductor deficit
The limiting transform in T. Nakamura, *A modified Riemann zeta distribution in
the critical strip*, Proc. Amer. Math. Soc. 143 (2015), 897–905, is recovered
from a single staircase at radix 2 and absolute integrability in the strip.
The finite-conductor deficit is the dilation from Sec. 4 of *Prime trees,
fractional parts, and zeta zeros*. -/

noncomputable section
open Set MeasureTheory
namespace RiemannResearch.RH.PrimeTreeMellinLaws

/-- Absolute convergence of the Mellin integral for the fractional part on the full strip. -/
theorem fract_mellin_convergent (s : ℂ) (hpos : 0 < s.re) (hlt : s.re < 1) :
    MellinConvergent (fun y : ℝ => ((Int.fract y : ℝ) : ℂ)) (-s) := by
  change IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ)) (Ioi 0)
  have hm : Measurable (fun x : ℝ => (x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.pow_const _).mul
      (Complex.measurable_ofReal.comp measurable_fract)
  have hnorm (x : ℝ) (hx : 0 < x) :
      ‖(x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ)‖ =
        x ^ (-s.re - 1) * Int.fract x := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
    simp
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  constructor
  · have hsmall : IntegrableOn (fun x : ℝ => x ^ (-s.re)) (Ioc (0 : ℝ) 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    apply hsmall.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hfl : (0 : ℝ) ≤ (⌊x⌋ : ℝ) := by
      exact_mod_cast (Int.floor_nonneg.mpr hx0.le)
    rw [hnorm x hx0]
    calc
      _ ≤ x ^ (-s.re - 1) * x :=
        mul_le_mul_of_nonneg_left (by unfold Int.fract; linarith) (Real.rpow_nonneg hx0.le _)
      _ = x ^ (-s.re - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
  · have hlarge : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    apply hlarge.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    rw [hnorm x hx0]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hx0.le _) (Int.fract_lt_one x).le

/-- Equation (11), retaining the actual fractional-part integral at every conductor. -/
theorem mellin_staircase_fract (D : ℕ) (hD : 0 < D) (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    mellin (fun y : ℝ => (staircase D y : ℂ)) (-s) =
      (1 - (D : ℂ) ^ (s - 1)) * mellin (fun y : ℝ => ((Int.fract y : ℝ) : ℂ)) (-s) := by
  let f (y : ℝ) : ℂ := (Int.fract y : ℝ)
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hi : MellinConvergent f (-s) := fract_mellin_convergent s hpos hlt
  have hj : MellinConvergent (fun y => f ((D : ℝ) * y)) (-s) :=
    (MellinConvergent.comp_mul_left hDr).mpr hi
  calc
    _ = mellin (fun y => f y - (D : ℂ)⁻¹ • f ((D : ℝ) * y)) (-s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      simp only [staircase_eq_fract D hD y (le_of_lt hy), Complex.ofReal_sub,
        Complex.ofReal_div, Complex.ofReal_natCast, f, smul_eq_mul]
      push_cast
      ring
    _ = _ := by
      rw [(hasMellin_sub hi (hj.const_smul (D : ℂ)⁻¹)).2, mellin_const_smul,
        mellin_comp_mul_left f (-s) hDr, neg_neg, Complex.ofReal_natCast,
        Complex.cpow_sub _ _ hDc, Complex.cpow_one]
      simp only [smul_eq_mul, f]
      ring

/-- Equation (24), proved through the finite radix-2 factor. -/
theorem mellin_fract_zeta (s : ℂ) (hpos : 0 < s.re) (hlt : s.re < 1) :
    mellin (fun y : ℝ => ((Int.fract y : ℝ) : ℂ)) (-s) = -riemannZeta s / s := by
  have hs1 : s ≠ 1 := by rintro rfl; simpa using hlt
  have hfac : 1 - (2 : ℂ) ^ (s - 1) ≠ 0 := by
    intro h
    have he := (sub_eq_zero.mp h).symm
    have hsmall : ‖(2 : ℂ) ^ (s - 1)‖ < 1 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        (by simpa only [Complex.sub_re, Complex.one_re] using sub_neg.mpr hlt)
    simpa only [he, norm_one, lt_self_iff_false] using hsmall
  apply mul_left_cancel₀ hfac
  simpa only [Nat.cast_ofNat] using
    (mellin_staircase_fract 2 (by decide) s hpos hlt).symm.trans
      (mellin_staircase_zeta 2 (by decide) s hpos hs1)

/-- Equation (12), strengthened to every complex Mellin exponent as an identity of
totalized Bochner integrals. At real exponent in (0,1) the integrals converge. -/
theorem mellin_staircase_abs_error (D : ℕ) (hD : 0 < D) (s : ℂ) :
    mellin (fun y : ℝ => ((|Int.fract y - staircase D y| : ℝ) : ℂ)) (-s) =
      (D : ℂ) ^ (s - 1) * mellin (fun y : ℝ => ((Int.fract y : ℝ) : ℂ)) (-s) := by
  let f (y : ℝ) : ℂ := (Int.fract y : ℝ)
  have hDr : 0 < (D : ℝ) := by exact_mod_cast hD
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  calc
    _ = mellin (fun y => f ((D : ℝ) * y) / (D : ℂ)) (-s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only
      rw [staircase_eq_fract D hD y (le_of_lt hy), sub_sub_cancel,
        abs_of_nonneg (div_nonneg (Int.fract_nonneg _) hDr.le),
        Complex.ofReal_div, Complex.ofReal_natCast]
    _ = _ := by
      rw [mellin_div_const, mellin_comp_mul_left f (-s) hDr, neg_neg, Complex.ofReal_natCast,
        Complex.cpow_sub _ _ hDc, Complex.cpow_one]
      simp only [smul_eq_mul, f]
      ring

end RiemannResearch.RH.PrimeTreeMellinLaws
