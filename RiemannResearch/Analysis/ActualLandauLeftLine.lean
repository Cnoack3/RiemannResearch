/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.ZeroCount.Basic
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.Hardy.TwoLine
import RiemannResearch.RH.WeilExplicitFormula.WeilEF.GammaRBracket
import RiemannResearch.Analysis.ActualRationalLandauRightLine
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import RiemannResearch.Analysis.ComplexLogIntegralBounds
import RiemannResearch.Analysis.ActualZetaGoodLandauHorizontals
import Mathlib.Tactic.GCongr

/-!
# Complete actual zeta left side for the fixed Landau contour

The full complex chi model has error <=6/t for t>=8. Exact oscillatory log
integration, the entire remainder and the complete reflected von Mangoldt
series give an unconditional finite left-line norm bound. The signed upward
left integral is split exactly before estimating; the contour subtracts it.
Source: the actual functional-equation, Gamma and Dirichlet-series providers;
Gonek's 1985 Theorem 1 supplies the standard contour strategy, not an imported
Landau bound: https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Complex Set MeasureTheory
open scoped BigOperators

namespace Zeta23.XiPrime.Hardy

/-- Actual chi logarithmic derivative on the fixed left side, with a complete
complex remainder. The leading term is real and the error is uniform. -/
theorem logDeriv_chiFE_neg_one_model_le (t : ℝ) (ht : 8 ≤ t) :
    ‖logDeriv chiFE ((-1 : ℂ) + t * I) +
      ((Real.log (t / (2 * Real.pi)) : ℝ) : ℂ)‖ ≤ 6 / t := by
  have ht0 : 0 < t := by linarith
  have him : ((-1 : ℂ) + t * I).im ≠ 0 := by simpa using ht0.ne'
  let s : ℂ := (-1 : ℂ) + t * I
  let q₁ : ℂ := 1 + ((-t / 2 : ℝ) : ℂ) * I
  let q₂ : ℂ := 1 / 2 + ((t / 2 : ℝ) : ℂ) * I
  let E₁ : ℂ := Complex.digamma q₁ - Complex.log (((-t / 2 : ℝ) : ℂ) * I)
  let E₂ : ℂ := Complex.digamma q₂ - Complex.log (((t / 2 : ℝ) : ℂ) * I)
  have hformula : logDeriv chiFE s = (Real.log Real.pi : ℂ) -
      (1 / 2 : ℂ) * Complex.digamma q₁ -
      (1 / 2 : ℂ) * Complex.digamma q₂ + 1 / s := by
    have hs : s.im ≠ 0 := him
    have hshift := logDeriv_Gammaℝ_shift hs
    rw [logDeriv_chiFE hs, hshift,
      Zeta23.WeilEF.logDeriv_Gammaℝ (s := 1 - s) (by simp [s]),
      Zeta23.WeilEF.logDeriv_Gammaℝ (s := s + 2) (by simp [s])]
    have hq₁ : (1 - s) / 2 = q₁ := by dsimp [s, q₁]; push_cast; ring
    have hq₂ : (s + 2) / 2 = q₂ := by dsimp [s, q₂]; push_cast; ring
    rw [hq₁, hq₂]
    ring
  have hb₁ := Complex.norm_digamma_sub_log_axis_le 1 (-t / 2) (by norm_num)
    (by simp only [abs_div, abs_neg, abs_of_pos ht0, abs_two]; linarith)
  have hb₂ := Complex.norm_digamma_sub_log_axis_le (1 / 2) (t / 2) (by norm_num)
    (by simp only [abs_div, abs_of_pos ht0, abs_two]; linarith)
  have he₁ : (1 : ℝ) / |-t / 2| + 1 / (2 * |-t / 2|) + 3 / (-t / 2) ^ 2 =
      3 / t + 12 / t ^ 2 := by
    simp only [abs_div, abs_neg, abs_of_pos ht0, abs_two]
    field_simp
    ring
  have he₂ : (1 / 2 : ℝ) / |t / 2| + 1 / (2 * |t / 2|) + 3 / (t / 2) ^ 2 =
      2 / t + 12 / t ^ 2 := by
    simp only [abs_div, abs_of_pos ht0, abs_two]
    field_simp
    ring
  rw [he₁] at hb₁
  rw [he₂] at hb₂
  have hE₁ : ‖E₁‖ ≤ 3 / t + 12 / t ^ 2 := by
    simpa only [E₁, q₁, Complex.ofReal_one] using hb₁
  have hE₂ : ‖E₂‖ ≤ 2 / t + 12 / t ^ 2 := by
    simpa only [E₂, q₂, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using hb₂
  have hpair := Complex.log_imaginary_axis_pair (t / 2) (by positivity)
  have hneg : (((-t / 2 : ℝ) : ℂ) * I) = (((t / 2 : ℝ) : ℂ) * (-I)) := by
    push_cast
    ring
  have hl : Real.log (t / (2 * Real.pi)) =
      Real.log (t / 2) - Real.log Real.pi := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
      Real.log_div (by positivity) Real.pi_ne_zero]
  have he : logDeriv chiFE s + ((Real.log (t / (2 * Real.pi)) : ℝ) : ℂ) =
      -(1 / 2 : ℂ) * (E₁ + E₂) + 1 / s := by
    rw [hformula, hl, Complex.ofReal_sub]
    dsimp [E₁, E₂]
    rw [hneg]
    linear_combination -(1 / 2 : ℂ) * hpair
  have hinv : ‖(1 : ℂ) / s‖ ≤ 1 / t := by
    rw [norm_div, norm_one]
    apply one_div_le_one_div_of_le ht0
    have h := Complex.abs_im_le_norm s
    simpa [s, abs_of_pos ht0] using h
  have hnum : (7 / 2 : ℝ) / t + 12 / t ^ 2 ≤ 6 / t := by
    rw [show (7 / 2 : ℝ) / t + 12 / t ^ 2 = ((7 / 2 : ℝ) * t + 12) / t ^ 2 by
      field_simp <;> ring,
      show (6 : ℝ) / t = (6 * t) / t ^ 2 by field_simp <;> ring]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  change ‖logDeriv chiFE s + ((Real.log (t / (2 * Real.pi)) : ℝ) : ℂ)‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖-(1 / 2 : ℂ) * (E₁ + E₂)‖ + ‖(1 : ℂ) / s‖ := norm_add_le _ _
    _ = (1 / 2) * ‖E₁ + E₂‖ + ‖(1 : ℂ) / s‖ := by
      rw [norm_mul]
      norm_num
    _ ≤ (1 / 2) * (‖E₁‖ + ‖E₂‖) + 1 / t := by
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)) hinv
    _ ≤ (1 / 2) * ((3 / t + 12 / t ^ 2) + (2 / t + 12 / t ^ 2)) + 1 / t := by
      gcongr
    _ = (7 / 2 : ℝ) / t + 12 / t ^ 2 := by ring
    _ ≤ 6 / t := hnum

end Zeta23.XiPrime.Hardy

namespace RiemannResearch.Analysis.ZeroOrdinate

/-- The upward left-side integral is separated into its exact actual chi
piece and reflected actual zeta piece. The contour uses its negative. -/
theorem integral_centered_left_logDeriv_split (A B u : ℝ) (hA : 0 < A) (hAB : A ≤ B) :
    (∫ t in A..B, Complex.exp ((u : ℂ) * ((-1 : ℂ) + t * I - 1 / 2)) *
      logDeriv riemannZeta ((-1 : ℂ) + t * I)) =
      (Real.exp (-3 * u / 2) : ℂ) *
        (∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
          logDeriv Zeta23.XiPrime.chiFE ((-1 : ℂ) + t * I)) -
      (Real.exp (-3 * u / 2) : ℂ) *
        (∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
          logDeriv riemannZeta ((2 : ℂ) - t * I)) := by
  have hphi : ∀ t : ℝ, Complex.exp ((u : ℂ) * ((-1 : ℂ) + t * I - 1 / 2)) =
      (Real.exp (-3 * u / 2) : ℂ) *
        Complex.exp (((u : ℂ) * I) * (t : ℂ)) := by
    intro t
    rw [show (u : ℂ) * ((-1 : ℂ) + t * I - 1 / 2) =
      ((-3 * u / 2 : ℝ) : ℂ) + (((u : ℂ) * I) * (t : ℂ)) by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp]
  have hchi : IntervalIntegrable (fun t : ℝ =>
      Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
        logDeriv Zeta23.XiPrime.chiFE ((-1 : ℂ) + t * I)) volume A B := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hAB] at ht
    have him : ((-1 : ℂ) + t * I).im ≠ 0 := by
      simp
      exact (lt_of_lt_of_le hA ht.1).ne'
    have hc := Zeta23.XiPrime.ZeroCount.continuousAt_logDeriv_of_analyticAt
      (Zeta23.XiPrime.Hardy.chiFE_analyticAt him) (Zeta23.XiPrime.Hardy.chiFE_ne_zero him)
    exact ((by fun_prop : ContinuousAt
      (fun t : ℝ => Complex.exp (((u : ℂ) * I) * (t : ℂ))) t).mul
        (hc.comp (x := t) (f := fun r : ℝ => (-1 : ℂ) + r * I) (by fun_prop))).continuousWithinAt
  have hzeta : IntervalIntegrable (fun t : ℝ =>
      Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
        logDeriv riemannZeta ((2 : ℂ) - t * I)) volume A B := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hc := Zeta23.XiPrime.ZeroCount.continuousAt_logDeriv_of_analyticAt
      (Zeta23.XiPrime.Hardy.analyticAt_riemannZeta (by intro h; have he := congrArg Complex.re h; norm_num at he : (2 : ℂ) - t * I ≠ 1))
      (riemannZeta_ne_zero_of_one_lt_re (by simp : 1 < ((2 : ℂ) - t * I).re))
    exact ((by fun_prop : ContinuousAt
      (fun t : ℝ => Complex.exp (((u : ℂ) * I) * (t : ℂ))) t).mul
        (hc.comp (x := t) (f := fun r : ℝ => (2 : ℂ) - r * I) (by fun_prop))).continuousWithinAt
  calc
    _ = ∫ t in A..B, (Real.exp (-3 * u / 2) : ℂ) *
        (Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
          logDeriv Zeta23.XiPrime.chiFE ((-1 : ℂ) + t * I) -
        Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
          logDeriv riemannZeta ((2 : ℂ) - t * I)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hAB] at ht
      have him : ((-1 : ℂ) + t * I).im ≠ 0 := by
        simp
        exact (lt_of_lt_of_le hA ht.1).ne'
      have hz := riemannZeta_ne_zero_of_one_lt_re
        (by simp : 1 < ((1 : ℂ) - ((-1 : ℂ) + t * I)).re)
      dsimp only
      rw [hphi, Zeta23.logDeriv_riemannZeta_functional him hz]
      have he : (1 : ℂ) - ((-1 : ℂ) + t * I) = (2 : ℂ) - t * I := by ring
      rw [he]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub hchi hzeta]
      ring

end RiemannResearch.Analysis.ZeroOrdinate



noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.Analysis.ZeroOrdinate

theorem reflected_two_neg_logDeriv_eq_tsum (t : ℝ) :
    -logDeriv riemannZeta ((2 : ℂ) - t * I) =
      ∑' k : ℕ, (mangoldtSquareCoeff k : ℂ) *
        Complex.exp ((((Real.log k : ℝ) : ℂ) * I) * (t : ℂ)) := by
  have h := centered_two_neg_logDeriv_eq_tsum 0 (-t)
  have hg : (2 : ℂ) + ((-t : ℝ) : ℂ) * I = (2 : ℂ) - t * I := by
    push_cast
    ring
  simp only [Complex.ofReal_zero, zero_mul, mul_zero, zero_div, Complex.exp_zero, one_mul,
    zero_sub, Real.exp_zero, Complex.ofReal_one] at h
  rw [hg] at h
  calc
    _ = ∑' k : ℕ, (mangoldtSquareCoeff k : ℂ) *
        Complex.exp ((((-Real.log k : ℝ) : ℂ) * I) * ((-t : ℝ) : ℂ)) := h
    _ = _ := by
      apply tsum_congr
      intro k
      congr 1
      congr 1
      push_cast
      ring

theorem phase_mul_reflected_two_neg_logDeriv_eq_tsum (u t : ℝ) :
    Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
        (-logDeriv riemannZeta ((2 : ℂ) - t * I)) =
      ∑' k : ℕ, (mangoldtSquareCoeff k : ℂ) *
        Complex.exp ((((u + Real.log k : ℝ) : ℂ) * I) * (t : ℂ)) := by
  rw [reflected_two_neg_logDeriv_eq_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro k
  calc
    _ = (mangoldtSquareCoeff k : ℂ) *
        (Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
          Complex.exp ((((Real.log k : ℝ) : ℂ) * I) * (t : ℂ))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 1
      congr 1
      push_cast
      ring

/-- Exact signed interval interchange, including all coefficients and endpoints. -/
theorem integral_phase_mul_reflected_two_neg_logDeriv_eq (A B u : ℝ) :
    (∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
      (-logDeriv riemannZeta ((2 : ℂ) - t * I))) =
      ∑' k : ℕ, (mangoldtSquareCoeff k : ℂ) *
        finitePhaseKernel A B (u + Real.log k) := by
  let F : ℕ → ℝ → ℂ := fun k t => (mangoldtSquareCoeff k : ℂ) *
    Complex.exp ((((u + Real.log k : ℝ) : ℂ) * I) * (t : ℂ))
  have hn : ∀ k t, ‖F k t‖ = mangoldtSquareCoeff k := by
    intro k t
    dsimp [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mangoldtSquareCoeff_nonneg k), Complex.norm_exp]
    have he : ((((u + Real.log k : ℝ) : ℂ) * I) * (t : ℂ)).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, zero_add, sub_zero]
    rw [he, Real.exp_zero, mul_one]
  have hs : ∀ t, Summable (fun k => F k t) := fun t =>
    summable_mangoldtSquareCoeff.of_norm_bounded (fun k => (hn k t).le)
  have hi : HasSum (fun k => ∫ t in A..B, F k t) (∫ t in A..B, ∑' k, F k t) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k (_ : ℝ) => mangoldtSquareCoeff k)
      (fun k => (show Continuous (F k) by dsimp [F]; fun_prop).aestronglyMeasurable)
    · intro k
      exact Filter.Eventually.of_forall fun t _ => (hn k t).le
    · exact Filter.Eventually.of_forall fun _ _ => summable_mangoldtSquareCoeff
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t _ => (hs t).hasSum
  calc
    _ = ∫ t in A..B, ∑' k, F k t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact phase_mul_reflected_two_neg_logDeriv_eq_tsum u t
    _ = ∑' k, ∫ t in A..B, F k t := hi.tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro k
      dsimp [F]
      rw [intervalIntegral.integral_const_mul, integral_phase_eq_finitePhaseKernel]

theorem norm_integral_phase_mul_reflected_two_neg_logDeriv_le
    (A B u : ℝ) (hu : 0 < u) :
    ‖∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
      (-logDeriv riemannZeta ((2 : ℂ) - t * I))‖ ≤
      (2 / u) * ∑' k : ℕ, mangoldtSquareCoeff k := by
  rw [integral_phase_mul_reflected_two_neg_logDeriv_eq]
  apply tsum_of_norm_bounded (summable_mangoldtSquareCoeff.hasSum.mul_left (2 / u))
  intro k
  by_cases hk : k = 0
  · subst k
    simp [mangoldtSquareCoeff]
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
    have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
    have hfreq : 0 < u + Real.log k := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mangoldtSquareCoeff_nonneg k)]
    calc
      _ ≤ mangoldtSquareCoeff k * (2 / |u + Real.log k|) :=
        mul_le_mul_of_nonneg_left (norm_finitePhaseKernel_le hfreq.ne' A B)
          (mangoldtSquareCoeff_nonneg k)
      _ ≤ mangoldtSquareCoeff k * (2 / u) := by
        rw [abs_of_pos hfreq]
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (by norm_num) hu (by linarith))
          (mangoldtSquareCoeff_nonneg k)
      _ = _ := mul_comm _ _

end RiemannResearch.Analysis.ZeroOrdinate



noncomputable section
open Complex Set MeasureTheory

namespace Zeta23.XiPrime.Hardy

def chiNegOneRemainder (t : ℝ) : ℂ :=
  logDeriv chiFE ((-1 : ℂ) + t * I) +
    ((Real.log t - Real.log (2 * Real.pi) : ℝ) : ℂ)

/-- Exact decomposition into the real log model and its entire actual complex
remainder, with both finite endpoints preserved. -/
theorem integral_phase_chi_neg_one_split (A B u : ℝ) (hA : 8 ≤ A) (hAB : A ≤ B) :
    (∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
      logDeriv chiFE ((-1 : ℂ) + t * I)) =
      -(∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
        ((Real.log t - Real.log (2 * Real.pi) : ℝ) : ℂ)) +
      ∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) * chiNegOneRemainder t := by
  have hpos : ∀ t ∈ Set.uIcc A B, 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le hAB] at ht
    linarith [ht.1]
  have hchi : IntervalIntegrable (fun t : ℝ =>
      Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
        logDeriv chiFE ((-1 : ℂ) + t * I)) volume A B := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have him : ((-1 : ℂ) + t * I).im ≠ 0 := by simpa using (hpos t ht).ne'
    have hc := Zeta23.XiPrime.ZeroCount.continuousAt_logDeriv_of_analyticAt
      (chiFE_analyticAt him) (chiFE_ne_zero him)
    exact ((by fun_prop : ContinuousAt
      (fun t : ℝ => Complex.exp (((u : ℂ) * I) * (t : ℂ))) t).mul
        (hc.comp (x := t) (f := fun r : ℝ => (-1 : ℂ) + r * I) (by fun_prop))).continuousWithinAt
  have hlog : IntervalIntegrable (fun t : ℝ =>
      Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
        ((Real.log t - Real.log (2 * Real.pi) : ℝ) : ℂ)) volume A B := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hc : ContinuousAt (fun t : ℝ =>
        ((Real.log t - Real.log (2 * Real.pi) : ℝ) : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt.comp
        ((Real.continuousAt_log (hpos t ht).ne').sub continuousAt_const)
    exact ((by fun_prop : ContinuousAt
      (fun t : ℝ => Complex.exp (((u : ℂ) * I) * (t : ℂ))) t).mul hc).continuousWithinAt
  have hs : (∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) * chiNegOneRemainder t) =
      (∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
        logDeriv chiFE ((-1 : ℂ) + t * I)) +
      (∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
        ((Real.log t - Real.log (2 * Real.pi) : ℝ) : ℂ)) := by
    simp_rw [chiNegOneRemainder, mul_add]
    exact intervalIntegral.integral_add hchi hlog
  linear_combination -hs

theorem norm_integral_phase_chiNegOneRemainder_le (A B u : ℝ)
    (hA : 8 ≤ A) (hAB : A ≤ B) :
    ‖∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) * chiNegOneRemainder t‖ ≤
      6 * Real.log (B / A) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le hA0 hAB
  have hb : ∀ t ∈ Set.Icc A B,
      ‖Complex.exp (((u : ℂ) * I) * (t : ℂ)) * chiNegOneRemainder t‖ ≤ 6 / t := by
    intro t ht
    have ht8 : 8 ≤ t := hA.trans ht.1
    have ht0 : 0 < t := by linarith
    have hmodel := logDeriv_chiFE_neg_one_model_le t ht8
    have hlog : Real.log (t / (2 * Real.pi)) =
        Real.log t - Real.log (2 * Real.pi) :=
      Real.log_div ht0.ne' (by positivity)
    rw [hlog] at hmodel
    rw [norm_mul, Complex.norm_exp]
    have he : (((u : ℂ) * I) * (t : ℂ)).re = 0 := by simp
    rw [he, Real.exp_zero, one_mul]
    exact hmodel
  have hg : IntervalIntegrable (fun t : ℝ => 6 / t) volume A B := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le hAB] at ht
    exact (lt_of_lt_of_le hA0 ht.1).ne'
  calc
    _ ≤ ∫ t in A..B, 6 / t := by
      apply intervalIntegral.norm_integral_le_of_norm_le hAB
        (Filter.Eventually.of_forall (fun t ht => hb t ⟨ht.1.le, ht.2⟩)) hg
    _ = _ := by
      rw [show (fun t : ℝ => 6 / t) = (fun t => 6 * (1 / t)) by funext t; ring,
        intervalIntegral.integral_const_mul, integral_one_div_of_pos hA0 hB0]

/-- The finite actual chi integral oscillates with its real log model. -/
theorem norm_integral_phase_chi_neg_one_le (A B u : ℝ)
    (hA : 8 ≤ A) (hAB : A ≤ B) (hu : 0 < u) :
    ‖∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
      logDeriv chiFE ((-1 : ℂ) + t * I)‖ ≤
      3 * Real.log B / u + 6 * Real.log (B / A) := by
  rw [integral_phase_chi_neg_one_split A B u hA hAB]
  have hq : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hqa : 2 * Real.pi ≤ A := by linarith [Real.pi_lt_four]
  have hmodel := Complex.norm_integral_exp_mul_log_sub_le A B u (2 * Real.pi) hAB hq hqa hu
  have hrem := norm_integral_phase_chiNegOneRemainder_le A B u hA hAB
  have hsum := norm_add_le
    (-(∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
      ((Real.log t - Real.log (2 * Real.pi) : ℝ) : ℂ)))
    (∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) * chiNegOneRemainder t)
  rw [norm_neg] at hsum
  linarith only [hsum, hmodel, hrem]

end Zeta23.XiPrime.Hardy


namespace RiemannResearch.Analysis.ZeroOrdinate

/-- The complete actual upward left line, after retaining its exact split. -/
theorem norm_integral_centered_left_logDeriv_le (A B u : ℝ)
    (hA : 8 ≤ A) (hAB : A ≤ B) (hu : 0 < u) :
    ‖∫ t in A..B, Complex.exp ((u : ℂ) * ((-1 : ℂ) + t * I - 1 / 2)) *
      logDeriv riemannZeta ((-1 : ℂ) + t * I)‖ ≤
      Real.exp (-3 * u / 2) *
        (3 * Real.log B / u + 6 * Real.log (B / A) +
          (2 / u) * ∑' k : ℕ, mangoldtSquareCoeff k) := by
  have hc := Zeta23.XiPrime.Hardy.norm_integral_phase_chi_neg_one_le A B u hA hAB hu
  have hz := norm_integral_phase_mul_reflected_two_neg_logDeriv_le A B u hu
  have he : (∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
      (-logDeriv riemannZeta ((2 : ℂ) - t * I))) =
      -(∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
        logDeriv riemannZeta ((2 : ℂ) - t * I)) := by
    simp_rw [mul_neg]
    rw [intervalIntegral.integral_neg]
  rw [he, norm_neg] at hz
  rw [integral_centered_left_logDeriv_split A B u (by linarith) hAB]
  calc
    _ ≤ ‖(Real.exp (-3 * u / 2) : ℂ) *
        (∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
          logDeriv Zeta23.XiPrime.chiFE ((-1 : ℂ) + t * I))‖ +
      ‖(Real.exp (-3 * u / 2) : ℂ) *
        (∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
          logDeriv riemannZeta ((2 : ℂ) - t * I))‖ := norm_sub_le _ _
    _ = Real.exp (-3 * u / 2) *
        (‖∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
          logDeriv Zeta23.XiPrime.chiFE ((-1 : ℂ) + t * I)‖ +
        ‖∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
          logDeriv riemannZeta ((2 : ℂ) - t * I)‖) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hc hz) (Real.exp_pos _).le

end RiemannResearch.Analysis.ZeroOrdinate
