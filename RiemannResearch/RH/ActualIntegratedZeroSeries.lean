import RiemannResearch.RH.WeilExplicitFormula.WeilEF.ZeroSummability
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Absolute convergence of the actual integrated zeta-zero kernel

Source: user-provided manuscript Prime_Phases_Agenda_Proof_Attempts.tex,
terminal-shell zero formula. This module proves only absolute convergence of its
actual zero series. It does not identify this series with the arithmetic
terminal mean, nor prove the requested O(x log(Y)/Y) truncation rate.

Actual zero multiplicities and their reciprocal-square summability are supplied
by the existing Zeta23 development, ultimately from a proved local zero count.
-/

noncomputable section
open Complex Set Filter Zeta23
open scoped BigOperators

namespace RiemannResearch.RH.ActualIntegratedZeroSeries

abbrev ActualZero := zetaZeroConfig.carrier

/-- The exact coefficient from the integrated terminal-shell expansion. -/
def term (x : ℝ) (ρ : ActualZero) : ℂ :=
  -(zeroMult ρ : ℂ) * Complex.exp ((ρ : ℂ) * (Real.log x : ℂ)) *
    (1 - Complex.exp (-(ρ : ℂ) * (Real.log 2 : ℂ))) / (ρ : ℂ) ^ 2

/-- An actual summable zero weight, with every multiplicity retained. -/
def weight (ρ : ActualZero) : ℝ :=
  (zeroMult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))

theorem summable_weight : Summable weight := by
  unfold weight
  change Summable (fun ρ : (zetaZeros zetaSeam).carrier =>
    (zeroMult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))
  exact Zeta23.WeilEF.zero_sum_inv_sq zetaSeam

private theorem strip (ρ : ActualZero) :
    0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
  have h : IsNontrivialZero (ρ : ℂ) := ρ.property
  exact ⟨h.2.1, h.2.2⟩

private theorem exp_x_norm_le (x : ℝ) (hx : 1 ≤ x) (ρ : ActualZero) :
    ‖Complex.exp ((ρ : ℂ) * (Real.log x : ℂ))‖ ≤ x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hre : (ρ : ℂ).re * Real.log x ≤ Real.log x := by
    have h := mul_le_mul_of_nonneg_right (strip ρ).2.le hlog
    simpa only [one_mul] using h
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  calc
    Real.exp ((ρ : ℂ).re * Real.log x) ≤ Real.exp (Real.log x) :=
      Real.exp_le_exp.mpr hre
    _ = x := Real.exp_log hx0

private theorem exp_neg_norm_le_one (ρ : ActualZero) :
    ‖Complex.exp (-(ρ : ℂ) * (Real.log 2 : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg (strip ρ).1.le hlog]

private theorem gamma_weight_comparison (ρ : ActualZero)
    (him : 1 ≤ |(ρ : ℂ).im|) :
    1 / ‖(ρ : ℂ)‖ ^ 2 ≤ 3 / (1 + Complex.normSq (gammaOf ρ)) := by
  have hstrip := strip ρ
  have hρnorm : 1 ≤ ‖(ρ : ℂ)‖ := him.trans (Complex.abs_im_le_norm _)
  have hρnormsq : 1 ≤ ‖(ρ : ℂ)‖ ^ 2 := by nlinarith [norm_nonneg (ρ : ℂ)]
  have hρsq : ‖(ρ : ℂ)‖ ^ 2 = (ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hgsq : Complex.normSq (gammaOf (ρ : ℂ)) =
      (ρ : ℂ).im ^ 2 + (1 / 2 - (ρ : ℂ).re) ^ 2 := by
    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re,
      Zeta23.WeilEF.gammaOf_im]
    ring
  have hge : 1 + Complex.normSq (gammaOf (ρ : ℂ)) ≤ 3 * ‖(ρ : ℂ)‖ ^ 2 := by
    rw [hgsq]
    nlinarith [sq_nonneg (ρ : ℂ).re, mul_nonneg hstrip.1.le (by linarith :
      0 ≤ 1 - (ρ : ℂ).re)]
  have hpos : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
    linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
  rw [div_le_div_iff₀ (by linarith : 0 < ‖(ρ : ℂ)‖ ^ 2) hpos]
  nlinarith

theorem term_norm_le (x : ℝ) (hx : 1 ≤ x) (ρ : ActualZero)
    (him : 1 ≤ |(ρ : ℂ).im|) :
    ‖term x ρ‖ ≤ (6 * x) * weight ρ := by
  have hmult : 0 ≤ (zeroMult ρ : ℝ) := Nat.cast_nonneg _
  have hfactor : ‖(1 : ℂ) - Complex.exp (-(ρ : ℂ) * (Real.log 2 : ℂ))‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ)
      (Complex.exp (-(ρ : ℂ) * (Real.log 2 : ℂ)))
    rw [norm_one] at h
    linarith [exp_neg_norm_le_one ρ]
  have hexp := exp_x_norm_le x hx ρ
  have hnum :
      (zeroMult ρ : ℝ) *
        ‖Complex.exp ((ρ : ℂ) * (Real.log x : ℂ))‖ *
        ‖(1 : ℂ) - Complex.exp (-(ρ : ℂ) * (Real.log 2 : ℂ))‖ ≤
      2 * x * (zeroMult ρ : ℝ) := by
    calc
      _ ≤ ((zeroMult ρ : ℝ) * x) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hexp hmult) hfactor
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    ‖term x ρ‖ =
        ((zeroMult ρ : ℝ) *
          ‖Complex.exp ((ρ : ℂ) * (Real.log x : ℂ))‖ *
          ‖(1 : ℂ) - Complex.exp (-(ρ : ℂ) * (Real.log 2 : ℂ))‖) /
          ‖(ρ : ℂ)‖ ^ 2 := by
      simp only [term, norm_div, norm_mul, norm_neg, Complex.norm_natCast,
        norm_pow]
    _ ≤ (2 * x * (zeroMult ρ : ℝ)) / ‖(ρ : ℂ)‖ ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = (2 * x * (zeroMult ρ : ℝ)) * (1 / ‖(ρ : ℂ)‖ ^ 2) := by ring
    _ ≤ (2 * x * (zeroMult ρ : ℝ)) *
        (3 / (1 + Complex.normSq (gammaOf ρ))) :=
      mul_le_mul_of_nonneg_left (gamma_weight_comparison ρ him) (by positivity)
    _ = (6 * x) * weight ρ := by unfold weight; ring

/-- The manuscript's actual integrated zero coefficients are absolutely summable.
The arithmetic explicit-formula identity is a separate unresolved obligation. -/
theorem absolutely_summable (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun ρ : ActualZero => ‖term x ρ‖) ∧ Summable (term x) := by
  have hg := summable_weight.mul_left (6 * x)
  have hfin : (zetaZeroConfig.window (-1) 1).Finite :=
    zetaZeroConfig.finite_window _ _
  have hSfin : ((fun ρ : ActualZero => (ρ : ℂ)) ⁻¹'
      (zetaZeroConfig.window (-1) 1)).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  have hb : ∀ᶠ ρ : ActualZero in cofinite,
      ‖term x ρ‖ ≤ (6 * x) * weight ρ := by
    filter_upwards [hSfin.compl_mem_cofinite] with ρ hρ
    have him : 1 ≤ |(ρ : ℂ).im| := by
      by_contra h
      have ht := abs_lt.mp (lt_of_not_ge h)
      apply hρ
      exact ⟨ρ.property, ht.1, ht.2.le⟩
    exact term_norm_le x hx ρ him
  have habs : Summable (fun ρ : ActualZero => ‖term x ρ‖) :=
    hg.of_norm_bounded_eventually (hb.mono (fun ρ hρ => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hρ))
  exact ⟨habs, habs.of_norm⟩

end RiemannResearch.RH.ActualIntegratedZeroSeries
