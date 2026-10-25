/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerPolynomialOrthonormal
import RiemannResearch.RH.QPrimePowerCofactorResidual
import RiemannResearch.RH.QPrimePowerValuationProjection
import RiemannResearch.RH.QSquarefreeCompleteBasis
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact legal cancellation between valuation and cofactor parts

Source: the user's generating-function polynomial-density research direction,
25 October 2026. These identities explain the separate arithmetic obligation.
The first valuation mode is already known to be nonlegal. Consequently legal
membership of the floor-log target requires cancellation of two nonzero legal
defects, and does not follow from completeness of the ambient valuation basis.
-/
noncomputable section
open scoped RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert QSquarefreeCompleteBasis

/-- The complete component orthogonal to the enlarged squarefree legal closure. -/
def squarefreeLegalDefect : QHilbert →L[ℝ] QHilbert :=
  ContinuousLinearMap.id ℝ QHilbert - closureWithConstants.starProjection

theorem squarefreeLegalDefect_eq (f : QHilbert) :
    squarefreeLegalDefect f = f - legalProjection f := rfl

theorem squarefreeLegalDefect_eq_zero_iff (f : QHilbert) :
    squarefreeLegalDefect f = 0 ↔ f ∈ closureWithConstants := by
  rw [squarefreeLegalDefect_eq, sub_eq_zero]
  constructor
  · intro h
    rw [h]
    exact legalProjection_mem f
  · intro h
    exact (legalProjection_eq_self h).symm

/-- Exact mean, first polynomial mode, and full cofactor decomposition. -/
theorem qTarget_polynomial_cofactor_decomposition (p : ℕ) (hp : p.Prime) :
    qTarget p hp.one_lt =
      inner ℝ (qTarget p hp.one_lt) qOne • qOne +
      ((p : ℝ) / ((p : ℝ)^2-1)) • valuationPolynomialMode p hp 0 +
      primeCofactorResidual p hp := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  have hc : ((p : ℝ) / ((p : ℝ)^2-1)) * (((p : ℝ)^2-1) / p) = 1 := by
    field_simp
  rw [valuationPolynomialMode_zero, primePowerProjectionUnit, smul_smul, hc, one_smul]
  unfold primeCofactorResidual
  module

/-- The mean is legal; both remaining legal defects must be retained. -/
theorem qTarget_squarefreeLegalDefect (p : ℕ) (hp : p.Prime) :
    squarefreeLegalDefect (qTarget p hp.one_lt) =
      ((p : ℝ) / ((p : ℝ)^2-1)) •
        squarefreeLegalDefect (valuationPolynomialMode p hp 0) +
      squarefreeLegalDefect (primeCofactorResidual p hp) := by
  conv_lhs => rw [qTarget_polynomial_cofactor_decomposition p hp]
  rw [map_add, map_add, map_smul, map_smul,
    (squarefreeLegalDefect_eq_zero_iff qOne).mpr qOne_mem_closureWithConstants,
    smul_zero, zero_add]

/-- The known square-jump obstruction gives a nonzero valuation legal defect. -/
theorem valuationPolynomialMode_zero_legalDefect_ne_zero (p : ℕ) (hp : p.Prime) :
    squarefreeLegalDefect (valuationPolynomialMode p hp 0) ≠ 0 := by
  rw [ne_eq, squarefreeLegalDefect_eq_zero_iff, valuationPolynomialMode_zero]
  exact primePowerProjectionUnit_not_mem_closureWithConstants p hp

/-- Necessary and sufficient arithmetic cancellation, with its sign unchanged. -/
theorem qTarget_mem_iff_legalDefect_cancellation (p : ℕ) (hp : p.Prime) :
    qTarget p hp.one_lt ∈ closureWithConstants ↔
      squarefreeLegalDefect (primeCofactorResidual p hp) =
        -(((p : ℝ) / ((p : ℝ)^2-1)) •
          squarefreeLegalDefect (valuationPolynomialMode p hp 0)) := by
  rw [← squarefreeLegalDefect_eq_zero_iff, qTarget_squarefreeLegalDefect p hp]
  constructor
  · intro h
    have hh := congrArg (fun v : QHilbert => v -
      ((p : ℝ) / ((p : ℝ)^2-1)) •
        squarefreeLegalDefect (valuationPolynomialMode p hp 0)) h
    simpa only [add_sub_cancel_left, zero_sub] using hh
  · intro h
    rw [h, add_neg_cancel]

/-- The legal error retains the signed cross term between projected defects. -/
theorem qTarget_legalDefect_energy_exact (p : ℕ) (hp : p.Prime) :
    ‖squarefreeLegalDefect (qTarget p hp.one_lt)‖^2 =
      ((p : ℝ) / ((p : ℝ)^2-1))^2 *
        ‖squarefreeLegalDefect (valuationPolynomialMode p hp 0)‖^2 +
      ‖squarefreeLegalDefect (primeCofactorResidual p hp)‖^2 +
      2 * ((p : ℝ) / ((p : ℝ)^2-1)) *
        inner ℝ (squarefreeLegalDefect (valuationPolynomialMode p hp 0))
          (squarefreeLegalDefect (primeCofactorResidual p hp)) := by
  rw [qTarget_squarefreeLegalDefect p hp, norm_add_sq_real, norm_smul,
    real_inner_smul_left, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- If the target is legal, the cofactor legal defect is necessarily nonzero. -/
theorem cofactor_legalDefect_ne_zero_of_qTarget_mem (p : ℕ) (hp : p.Prime)
    (h : qTarget p hp.one_lt ∈ closureWithConstants) :
    squarefreeLegalDefect (primeCofactorResidual p hp) ≠ 0 := by
  rw [(qTarget_mem_iff_legalDefect_cancellation p hp).mp h]
  apply neg_ne_zero.mpr
  apply smul_ne_zero
  · have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    apply div_ne_zero <;> nlinarith
  · exact valuationPolynomialMode_zero_legalDefect_ne_zero p hp

/-- The two projected defects have strictly negative pairing if the target is legal. -/
theorem legalDefect_inner_neg_of_qTarget_mem (p : ℕ) (hp : p.Prime)
    (h : qTarget p hp.one_lt ∈ closureWithConstants) :
    inner ℝ (squarefreeLegalDefect (valuationPolynomialMode p hp 0))
      (squarefreeLegalDefect (primeCofactorResidual p hp)) < 0 := by
  rw [(qTarget_mem_iff_legalDefect_cancellation p hp).mp h,
    inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  apply neg_lt_zero.mpr
  apply mul_pos
  · have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    apply div_pos <;> nlinarith
  · exact sq_pos_of_pos (norm_pos_iff.mpr
      (valuationPolynomialMode_zero_legalDefect_ne_zero p hp))

/-- Legal Parseval saturation is exactly the same signed cancellation condition. -/
theorem qTarget_legal_parseval_iff_cancellation (p : ℕ) (hp : p.Prime) :
    (∑' i : LegalIndex, (inner ℝ (qTarget p hp.one_lt) (legalVector i))^2) =
      ‖qTarget p hp.one_lt‖^2 ↔
    squarefreeLegalDefect (primeCofactorResidual p hp) =
      -(((p : ℝ) / ((p : ℝ)^2-1)) •
        squarefreeLegalDefect (valuationPolynomialMode p hp 0)) := by
  rw [← mem_closureWithConstants_iff_parseval, qTarget_mem_iff_legalDefect_cancellation]

end RiemannResearch.RH.PrimePowerTarget
