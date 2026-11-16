/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ComplexIntegralLogLift
import RiemannResearch.RH.WeilExplicitFormula.GammaFacts.StirlingVert
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A uniform vertical Gamma quotient bound

The exact horizontal logarithmic identity precedes the estimate. For
`0 < a ≤ b ≤ 1` and `1/2 ≤ |t|`, the estimate is uniform in both abscissae:

`‖Gamma (b + it) / Gamma (a + it)‖ ≤ exp (5 * (b-a) / t^2) * |t|^(b-a)`.

The extension below permits either order of a and b in (0,1], proving
both upper and lower bounds with exp(+-5 |b-a|/t^2) and the signed
power |t|^(b-a). It supplies the negative exponents required on the
right zeta-square Mellin contour.

The frequency restriction is explicit: no assertion about the remaining
compact range is supplied by this estimate. This is an unconditional Gamma
ingredient of the symmetric shifted-zeta estimate in Báez-Duarte,
*A strengthening of the Nyman-Beurling criterion for the Riemann Hypothesis, 2*,
Lemma 2.2,
https://arxiv.org/abs/math/0205003. The proof uses the existing proved
vertical digamma Stirling estimate and a differentiable logarithm lift.
It does not establish convergence of finite Möbius approximants in L².
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Complex
open scoped Interval

namespace RiemannResearch.Analysis.GammaRatioVertical

private theorem gamma_analyticAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.Gamma z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hz] with w hw
  apply Complex.differentiableAt_Gamma
  intro n hn
  have he := congrArg Complex.re hn
  simp only [Complex.neg_re, Complex.natCast_re] at he
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private theorem continuousOn_re_digamma_horizontal {a b t : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x : ℝ => (Complex.digamma ((x : ℂ) + I * t)).re)
      (Icc a b) := by
  intro x hx
  have hz : 0 < ((x : ℂ) + I * t).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero, add_zero] using ha.trans_le hx.1
  have hg := gamma_analyticAt_of_re_pos hz
  have hquot := hg.deriv.continuousAt.div hg.continuousAt
    (Complex.Gamma_ne_zero_of_re_pos hz)
  have harg : Continuous (fun u : ℝ => (u : ℂ) + I * t) := by fun_prop
  have hcomp : ContinuousAt (fun u : ℝ =>
      deriv Complex.Gamma ((u : ℂ) + I * t) /
        Complex.Gamma ((u : ℂ) + I * t)) x :=
    hquot.comp (f := fun u : ℝ => (u : ℂ) + I * t)
      (x := x) harg.continuousAt
  have hh : ContinuousAt (fun u : ℝ =>
      (deriv Complex.Gamma ((u : ℂ) + I * t) /
        Complex.Gamma ((u : ℂ) + I * t)).re) x :=
    Complex.continuous_re.continuousAt.comp (x := x)
      (f := fun u : ℝ => deriv Complex.Gamma ((u : ℂ) + I * t) /
        Complex.Gamma ((u : ℂ) + I * t)) hcomp
  simpa only [Complex.digamma_def, logDeriv_apply] using hh.continuousWithinAt

/-- Exact horizontal logarithmic identity, with no large-height assumption. -/
theorem log_norm_Gamma_sub_eq_integral_digamma {a b t : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Real.log ‖Complex.Gamma ((b : ℂ) + I * t)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + I * t)‖ =
      ∫ x in a..b, (Complex.digamma ((x : ℂ) + I * t)).re := by
  have hpos : ∀ x ∈ Icc a b, 0 < ((x : ℂ) + I * t).re := by
    intro x hx
    simpa using ha.trans_le hx.1
  have hga : ∀ x ∈ Icc a b,
      AnalyticAt ℂ Complex.Gamma ((x : ℂ) * 1 + I * t) := by
    intro x hx
    simpa only [mul_one] using gamma_analyticAt_of_re_pos (hpos x hx)
  obtain ⟨hp, hp'⟩ := Complex.analytic_affine_path_C1 1 (I * t) hga
  simp only [mul_one] at hp hp'
  have hne : ∀ x ∈ Icc a b, Complex.Gamma ((x : ℂ) + I * t) ≠ 0 :=
    fun x hx => Complex.Gamma_ne_zero_of_re_pos (hpos x hx)
  obtain ⟨L, _hLc, _hLa, hLe, hLd⟩ :=
    Complex.exists_logLift_of_nonzero hab hp hp' hne
  have hLre : ∀ x ∈ Icc a b,
      HasDerivAt (fun u => (L u).re)
        (Complex.digamma ((x : ℂ) + I * t)).re x := by
    intro x hx
    have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hLd x hx)
    simpa only [Complex.digamma_def, logDeriv_apply] using! hh
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b)
    (fun x hx => hLre x (by simpa only [uIcc_of_le hab] using hx))
    ((continuousOn_re_digamma_horizontal (b := b) (t := t) ha).intervalIntegrable_of_Icc hab)
  rw [Complex.logLift_re_eq_log_norm (L := L)
      (p := fun u : ℝ => Complex.Gamma ((u : ℂ) + I * t)) (hLe b ⟨hab, le_rfl⟩),
    Complex.logLift_re_eq_log_norm (L := L)
      (p := fun u : ℝ => Complex.Gamma ((u : ℂ) + I * t)) (hLe a ⟨le_rfl, hab⟩)] at hFTC
  exact hFTC.symm

/-- The horizontal logarithmic quotient bound obtained by integrating the
existing explicit vertical Stirling error. -/
theorem log_norm_Gamma_sub_le {a b t : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b ≤ 1) (ht : 1 / 2 ≤ |t|) :
    Real.log ‖Complex.Gamma ((b : ℂ) + I * t)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + I * t)‖ ≤
      (b - a) * (Real.log |t| + 5 / t ^ 2) := by
  rw [log_norm_Gamma_sub_eq_integral_digamma ha hab]
  calc
    _ ≤ ∫ _x in a..b, Real.log |t| + 5 / t ^ 2 := by
      apply intervalIntegral.integral_mono_on hab
        ((continuousOn_re_digamma_horizontal (b := b) (t := t) ha).intervalIntegrable_of_Icc hab)
        intervalIntegrable_const
      intro x hx
      have hh := Zeta23.StirlingVert.re_digamma_stirling'
        (ha.trans_le hx.1) (hx.2.trans hb) ht
      linarith [(abs_le.mp hh).2]
    _ = (b - a) * (Real.log |t| + 5 / t ^ 2) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]

/-- Uniform vertical Gamma quotient estimate for all positive abscissae up
to one. The constant and the complete finite-height error are explicit. -/
theorem norm_Gamma_ratio_le {a b t : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b ≤ 1) (ht : 1 / 2 ≤ |t|) :
    ‖Complex.Gamma ((b : ℂ) + I * t) /
        Complex.Gamma ((a : ℂ) + I * t)‖ ≤
      Real.exp (5 * (b - a) / t ^ 2) * |t| ^ (b - a) := by
  have hapos : 0 < ((a : ℂ) + I * t).re := by simpa using ha
  have hbpos : 0 < ((b : ℂ) + I * t).re := by simpa using ha.trans_le hab
  have hna : 0 < ‖Complex.Gamma ((a : ℂ) + I * t)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hapos)
  have hnb : 0 < ‖Complex.Gamma ((b : ℂ) + I * t)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hbpos)
  have htpos : 0 < |t| := by linarith
  calc
    _ = Real.exp (Real.log ‖Complex.Gamma ((b : ℂ) + I * t)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + I * t)‖) := by
      rw [norm_div, Real.exp_sub, Real.exp_log hna, Real.exp_log hnb]
    _ ≤ Real.exp ((b - a) * (Real.log |t| + 5 / t ^ 2)) :=
      Real.exp_le_exp.mpr (log_norm_Gamma_sub_le ha hab hb ht)
    _ = Real.exp (5 * (b - a) / t ^ 2) * |t| ^ (b - a) := by
      rw [Real.rpow_def_of_pos htpos, ← Real.exp_add]
      congr 1
      ring

/-- The symmetric abscissae occurring in the zeta functional equation.
This is still solely a Gamma theorem and assumes no zero-free statement. -/
theorem norm_Gamma_symmetric_ratio_le {ε t : ℝ}
    (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2) (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (((1 / 4 + ε / 2 : ℝ) : ℂ) + I * (t / 2)) /
        Complex.Gamma (((1 / 4 - ε / 2 : ℝ) : ℂ) + I * (t / 2))‖ ≤
      Real.exp (20 * ε / t ^ 2) * (|t| / 2) ^ ε := by
  have ha : (0 : ℝ) < 1 / 4 - ε / 2 := by linarith
  have hab : (1 / 4 - ε / 2 : ℝ) ≤ 1 / 4 + ε / 2 := by linarith
  have hb : (1 / 4 + ε / 2 : ℝ) ≤ 1 := by linarith
  have ht' : (1 / 2 : ℝ) ≤ |t / 2| := by
    rw [abs_div, abs_two]
    linarith
  have hh := norm_Gamma_ratio_le ha hab hb ht'
  have he : (1 / 4 + ε / 2 : ℝ) - (1 / 4 - ε / 2) = ε := by ring
  have hf : (5 * ε / (t / 2) ^ 2 : ℝ) = 20 * ε / t ^ 2 := by ring
  simpa only [he, hf, abs_div, abs_two, Complex.ofReal_div,
    Complex.ofReal_ofNat] using hh


/-- The lower horizontal Stirling estimate, retaining the signed logarithmic
main term. -/
theorem log_norm_Gamma_sub_ge {a b t : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b ≤ 1) (ht : 1 / 2 ≤ |t|) :
    (b - a) * (Real.log |t| - 5 / t ^ 2) ≤
      Real.log ‖Complex.Gamma ((b : ℂ) + I * t)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + I * t)‖ := by
  rw [log_norm_Gamma_sub_eq_integral_digamma ha hab]
  calc
    _ = ∫ _x in a..b, Real.log |t| - 5 / t ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
        ((continuousOn_re_digamma_horizontal (b := b) (t := t) ha).intervalIntegrable_of_Icc hab)
      intro x hx
      have hh := Zeta23.StirlingVert.re_digamma_stirling'
        (ha.trans_le hx.1) (hx.2.trans hb) ht
      linarith [(abs_le.mp hh).1]

/-- A two-sided logarithmic Gamma quotient estimate, with either order of
the abscissae. This also controls the inverse quotient without losing the
sign of the power of the height. -/
theorem abs_log_norm_Gamma_ratio_error_le {a b t : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (ht : 1 / 2 ≤ |t|) :
    abs ((Real.log ‖Complex.Gamma ((b : ℂ) + I * t)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + I * t)‖) -
      (b - a) * Real.log |t|) ≤ 5 * |b - a| / t ^ 2 := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    have hu := log_norm_Gamma_sub_le ha hab hb1 ht
    have hl := log_norm_Gamma_sub_ge ha hab hb1 ht
    simp only [div_eq_mul_inv] at hu hl ⊢
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  · rw [abs_of_nonpos (sub_nonpos.mpr hba)]
    have hu := log_norm_Gamma_sub_le hb hba ha1 ht
    have hl := log_norm_Gamma_sub_ge hb hba ha1 ht
    simp only [div_eq_mul_inv] at hu hl ⊢
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- Uniform Gamma quotient bound for arbitrary positive abscissae up to
one. In particular, the height exponent may be negative. -/
theorem norm_Gamma_ratio_le_of_pos {a b t : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (ht : 1 / 2 ≤ |t|) :
    ‖Complex.Gamma ((b : ℂ) + I * t) /
        Complex.Gamma ((a : ℂ) + I * t)‖ ≤
      Real.exp (5 * |b - a| / t ^ 2) * |t| ^ (b - a) := by
  have hna : 0 < ‖Complex.Gamma ((a : ℂ) + I * t)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simpa using ha))
  have hnb : 0 < ‖Complex.Gamma ((b : ℂ) + I * t)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simpa using hb))
  have htpos : 0 < |t| := by linarith
  have hh := (abs_le.mp (abs_log_norm_Gamma_ratio_error_le ha ha1 hb hb1 ht)).2
  calc
    _ = Real.exp (Real.log ‖Complex.Gamma ((b : ℂ) + I * t)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + I * t)‖) := by
      rw [norm_div, Real.exp_sub, Real.exp_log hna, Real.exp_log hnb]
    _ ≤ Real.exp (5 * |b - a| / t ^ 2 + (b - a) * Real.log |t|) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [Real.rpow_def_of_pos htpos, ← Real.exp_add]
      congr 1
      ring

/-- The matching lower bound, with the same explicit error. -/
theorem le_norm_Gamma_ratio_of_pos {a b t : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (ht : 1 / 2 ≤ |t|) :
    Real.exp (-(5 * |b - a| / t ^ 2)) * |t| ^ (b - a) ≤
      ‖Complex.Gamma ((b : ℂ) + I * t) /
        Complex.Gamma ((a : ℂ) + I * t)‖ := by
  have hna : 0 < ‖Complex.Gamma ((a : ℂ) + I * t)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simpa using ha))
  have hnb : 0 < ‖Complex.Gamma ((b : ℂ) + I * t)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simpa using hb))
  have htpos : 0 < |t| := by linarith
  have hh := (abs_le.mp (abs_log_norm_Gamma_ratio_error_le ha ha1 hb hb1 ht)).1
  calc
    _ = Real.exp (-(5 * |b - a| / t ^ 2) + (b - a) * Real.log |t|) := by
      rw [Real.rpow_def_of_pos htpos, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Real.log ‖Complex.Gamma ((b : ℂ) + I * t)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + I * t)‖) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [norm_div, Real.exp_sub, Real.exp_log hna, Real.exp_log hnb]

/-- Both symmetric directions, including the negative exponents needed
on the right-hand zeta-square Mellin contour. -/
theorem norm_Gamma_symmetric_ratio_le_of_abs_lt {ε t : ℝ}
    (hε : |ε| < 1 / 2) (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (((1 / 4 + ε / 2 : ℝ) : ℂ) + I * (t / 2)) /
        Complex.Gamma (((1 / 4 - ε / 2 : ℝ) : ℂ) + I * (t / 2))‖ ≤
      Real.exp (20 * |ε| / t ^ 2) * (|t| / 2) ^ ε := by
  have he := abs_lt.mp hε
  have ht' : (1 / 2 : ℝ) ≤ |t / 2| := by
    rw [abs_div, abs_two]
    linarith
  have hh := norm_Gamma_ratio_le_of_pos
    (a := 1 / 4 - ε / 2) (b := 1 / 4 + ε / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) ht'
  have heq : (1 / 4 + ε / 2 : ℝ) - (1 / 4 - ε / 2) = ε := by ring
  have hf : (5 * |ε| / (t / 2) ^ 2 : ℝ) = 20 * |ε| / t ^ 2 := by ring
  simpa only [heq, hf, abs_div, abs_two, Complex.ofReal_div,
    Complex.ofReal_ofNat] using hh
end RiemannResearch.Analysis.GammaRatioVertical
