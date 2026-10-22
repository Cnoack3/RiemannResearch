/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoHorizontalZeroBridge
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.ExplicitFormula.ZeroFree
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual all-sign reciprocal zero sum and its explicit constant

Source: the paper-first continuation of 11 October 2026, Section 5.1.
The classical constant is evaluated using the actual regularized entire xi,
not a totalized pole-cancelling expression. The paired-sum provider is the
unconditional contour theorem `Zeta23.XiPrime.ZeroFree.logDeriv_xi_sub_reflect`.
Every distinct actual nontrivial zero occurs once, weighted by `zeroMult`,
with both signs of the ordinate. No RH, zero simplicity, or Hadamard-product
hypothesis is introduced.

The endpoint theorem `completedRiemannZeta₀_one` was source-confirmed in
Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean at the project's pinned revision
51e6992efd06126df61a496bebf8f49482a4e129 (v4.33.0-rc2).
The project paired-sum declarations were source-confirmed in
RH/WeilExplicitFormula/XiPrime/ExplicitFormula/ZeroFree.lean.

-/

noncomputable section
open Complex Zeta23
open scoped BigOperators ComplexConjugate

namespace RiemannResearch.Analysis.ActualZeroReciprocalConstant

open Zeta23.XiPrime Zeta23.XiPrime.ZeroFree
open ActualZeroHorizontalEnergy
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ParetoBeurlingMellinObstruction
open RiemannResearch.RH.ParetoHorizontalZeroBridge

/-- The exact constant uses the conventional all-sign zero normalization. -/
def reciprocalConstant : ℝ :=
  2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

/-- Differentiate the regularized entire xi at the removable endpoint. -/
theorem deriv_xi_one_eq_completed :
    deriv xi (1 : ℂ) = completedRiemannZeta₀ 1 / 2 := by
  have hp : HasDerivAt (fun s : ℂ => s * (s - 1) / 2) (1 / 2) 1 := by
    simpa using (((hasDerivAt_id (1 : ℂ)).mul
      ((hasDerivAt_id (1 : ℂ)).sub_const 1)).div_const 2)
  have h := (hp.mul (differentiable_completedZeta₀ 1).hasDerivAt).add_const (1 / 2 : ℂ)
  change HasDerivAt xi _ (1 : ℂ) at h
  calc
    deriv xi (1 : ℂ) = _ := h.deriv
    _ = completedRiemannZeta₀ 1 / 2 := by ring

/-- The endpoint logarithmic derivative is evaluated without a Laurent premise. -/
theorem logDeriv_xi_one_eq_constant :
    logDeriv xi (1 : ℂ) = (reciprocalConstant : ℂ) / 2 := by
  rw [logDeriv_apply, deriv_xi_one_eq_completed, xi_one]
  have hc : completedRiemannZeta₀ (1 : ℂ) = (reciprocalConstant : ℂ) / 2 := by
    rw [completedRiemannZeta₀_one]
    have hlog : Complex.log (4 * (Real.pi : ℂ)) =
        (Real.log (4 * Real.pi) : ℂ) := by
      rw [show (4 : ℂ) * (Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ) by norm_cast,
        ← Complex.ofReal_log (by positivity : 0 ≤ 4 * Real.pi)]
    rw [hlog]
    simp only [reciprocalConstant, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_ofNat]
    ring
  rw [hc]
  ring

private theorem xi_one_ne_zero : xi (1 : ℂ) ≠ 0 := by
  rw [xi_one]
  norm_num

/-- Raw-complex version of the endpoint contour weight, independent of the
definitional presentation of the actual zero subtype. -/
theorem wt_one_eq_reciprocal_of_nontrivial {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    wt (1 : ℂ) ρ = 1 / (ρ * (1 - ρ)) := by
  have h0 : ρ ≠ 0 := by
    intro h
    simpa [h] using hρ.2.1
  have h1 : 1 - ρ ≠ 0 := by
    intro h
    have he : ρ = 1 := (sub_eq_zero.mp h).symm
    simpa [he] using hρ.2.2
  have hr : reflect (1 : ℂ) = 0 := by simp [reflect]
  rw [wt, hr]
  simp only [zero_sub, div_neg, sub_neg_eq_add]
  field_simp [h0, h1]
  ring

/-- The contour weight at one is exactly the reciprocal zero-pair factor. -/
theorem wt_one_eq_reciprocal (ρ : ActualZero) :
    wt (1 : ℂ) (ρ : ℂ) = 1 / ((ρ : ℂ) * (1 - (ρ : ℂ))) :=
  wt_one_eq_reciprocal_of_nontrivial ρ.property

/-- Absolute convergence retains analytic multiplicities and both ordinate signs. -/
theorem paired_reciprocal_summable :
    Summable (fun ρ : ActualZero =>
      (zeroMult (ρ : ℂ) : ℂ) / ((ρ : ℂ) * (1 - (ρ : ℂ)))) := by
  refine (summable_wt xi_one_ne_zero).congr ?_
  intro ρ
  rw [wt_one_eq_reciprocal_of_nontrivial ρ.property]
  ring

/-- Exact actual-zeta reciprocal-pair sum; no product provider is assumed. -/
theorem paired_reciprocal_tsum :
    (∑' ρ : ActualZero,
      (zeroMult (ρ : ℂ) : ℂ) / ((ρ : ℂ) * (1 - (ρ : ℂ)))) =
      (reciprocalConstant : ℂ) := by
  have h := logDeriv_xi_sub_reflect xi_one_ne_zero
  have hr : reflect (1 : ℂ) = 0 := by simp [reflect]
  have hz : logDeriv xi (0 : ℂ) = -logDeriv xi (1 : ℂ) := by
    simpa only [sub_self] using logDeriv_xi_one_sub (1 : ℂ)
  rw [hr, hz, logDeriv_xi_one_eq_constant] at h
  calc
    _ = ∑' ρ : ActualZero, (zeroMult (ρ : ℂ) : ℂ) * wt (1 : ℂ) (ρ : ℂ) := by
      apply tsum_congr
      intro ρ
      rw [wt_one_eq_reciprocal]
      ring
    _ = (reciprocalConstant : ℂ) / 2 - -((reciprocalConstant : ℂ) / 2) := h.symm
    _ = _ := by ring

private theorem reciprocal_pair_lower (β γ : ℝ) (h0 : 0 < β) (h1 : β < 1) :
    1 / (1 + γ ^ 2) ≤
      (1 - β) / ((1 - β) ^ 2 + γ ^ 2) + β / (β ^ 2 + γ ^ 2) := by
  have hc : 0 < 1 - β := by linarith
  have hm := mul_nonneg h0.le hc.le
  have hd0 : 0 < β ^ 2 + γ ^ 2 := by positivity
  have hd1 : 0 < (1 - β) ^ 2 + γ ^ 2 := by positivity
  have hW : 0 < 1 + γ ^ 2 := by positivity
  have hD0 : β ^ 2 + γ ^ 2 ≤ 1 + γ ^ 2 := by nlinarith
  have hD1 : (1 - β) ^ 2 + γ ^ 2 ≤ 1 + γ ^ 2 := by nlinarith
  have ha : β / (1 + γ ^ 2) ≤ β / (β ^ 2 + γ ^ 2) :=
    (div_le_div_iff₀ hW hd0).mpr (mul_le_mul_of_nonneg_left hD0 h0.le)
  have hb : (1 - β) / (1 + γ ^ 2) ≤
      (1 - β) / ((1 - β) ^ 2 + γ ^ 2) :=
    (div_le_div_iff₀ hW hd1).mpr (mul_le_mul_of_nonneg_left hD1 hc.le)
  calc
    _ = (1 - β) / (1 + γ ^ 2) + β / (1 + γ ^ 2) := by ring
    _ ≤ _ := add_le_add hb ha

/-- Each ordinate weight is dominated by the real reciprocal-pair factor. -/
theorem ordinateTerm_le_reciprocal_re (ρ : ActualZero) :
    ordinateInverseSquareTerm ρ ≤
      ((zeroMult (ρ : ℂ) : ℂ) / ((ρ : ℂ) * (1 - (ρ : ℂ)))).re := by
  have h := reciprocal_pair_lower (ρ : ℂ).re (ρ : ℂ).im
    ρ.property.2.1 ρ.property.2.2
  have hw : (wt (1 : ℂ) (ρ : ℂ)).re =
      (1 - (ρ : ℂ).re) / ((1 - (ρ : ℂ).re) ^ 2 + (ρ : ℂ).im ^ 2) +
        (ρ : ℂ).re / ((ρ : ℂ).re ^ 2 + (ρ : ℂ).im ^ 2) := by
    rw [re_wt, re_one_div, re_one_div]
    simp only [Complex.one_re, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.one_im, Zeta23.reflect_re, Zeta23.reflect_im,
      sub_sub_cancel, zero_sub]
    simp only [pow_two, neg_mul_neg]
  rw [← hw] at h
  have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (zeroMult (ρ : ℂ)))
  have hc : (zeroMult (ρ : ℂ) : ℂ) = ((zeroMult (ρ : ℂ) : ℝ) : ℂ) := by
    norm_cast
  rw [wt_one_eq_reciprocal] at hm
  rw [div_eq_mul_inv, hc, Complex.re_ofReal_mul]
  simpa [ordinateInverseSquareTerm, div_eq_mul_inv] using hm

/-- Explicit all-sign bound on the actual ordinate reciprocal-square sum. -/
theorem ordinateInverseSquareSum_le_constant :
    ordinateInverseSquareSum ≤ reciprocalConstant := by
  have hs := (Complex.hasSum_re paired_reciprocal_summable.hasSum).summable
  have h := ordinateInverseSquareTerm_summable.tsum_le_tsum
    ordinateTerm_le_reciprocal_re hs
  rw [← Complex.re_tsum paired_reciprocal_summable,
    paired_reciprocal_tsum, Complex.ofReal_re] at h
  exact h

/-- The explicit paper bridge applies to the actual legal Pareto closure. -/
theorem horizontalFourthEnergy_le_pareto_error_constant
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure) :
    horizontalFourthEnergy ≤ (reciprocalConstant / 4) * ‖hilbertOne - f‖ ^ 2 :=
  horizontalFourthEnergy_le_of_ordinate_sum_le f hf reciprocalConstant
    ordinateInverseSquareSum_le_constant

/-- The constant is nonnegative from its actual zero-sum majorization. -/
theorem reciprocalConstant_nonneg : 0 ≤ reciprocalConstant :=
  le_trans ordinateInverseSquareSum_nonneg ordinateInverseSquareSum_le_constant

/-- Strict positivity comes from the actual nonempty zero sum, without a
numerical estimate for Euler's constant or the logarithm. -/
theorem reciprocalConstant_pos : 0 < reciprocalConstant := by
  have h := Zeta23.XiPrime.re_logDeriv_xi_pos
    (s := (1 : ℂ)) (by norm_num)
  rw [logDeriv_xi_one_eq_constant] at h
  have he : ((reciprocalConstant : ℂ) / 2).re = reciprocalConstant / 2 := by
    norm_num [Complex.div_re]
  rw [he] at h
  linarith

/-- Explicit residual lower bound for every actual legal Pareto candidate. -/
theorem pareto_error_lower_bound_of_horizontalFourthEnergy
    (f : ThresholdHilbert) (hf : f ∈ normalizedResidueClosure) :
    4 * horizontalFourthEnergy / reciprocalConstant ≤ ‖hilbertOne - f‖ ^ 2 := by
  apply (div_le_iff₀ reciprocalConstant_pos).mpr
  have h := horizontalFourthEnergy_le_pareto_error_constant f hf
  nlinarith only [h]

/-- The detecting energy bounds the repository's actual full inverse-Gram
captured energy at every stage. -/
theorem canonicalCaptured_le_one_sub_horizontalFourthEnergy (n : ℕ) :
    RiemannResearch.RH.Pareto.CoefficientStabilization.ProjectionSchur.captured n ≤
      1 - 4 * horizontalFourthEnergy / reciprocalConstant := by
  have h := pareto_error_lower_bound_of_horizontalFourthEnergy
    (RiemannResearch.RH.Pareto.CoefficientStabilization.projection n)
    (canonicalProjection_mem_normalizedResidueClosure n)
  rw [RiemannResearch.RH.Pareto.CoefficientStabilization.ProjectionSchur.error_eq_one_sub_captured]
    at h
  linarith

end RiemannResearch.Analysis.ActualZeroReciprocalConstant
