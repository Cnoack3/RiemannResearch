/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ChebyshevEnergy
import RiemannResearch.RH.QSquarefreeDisplacementResolvent
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-!
# Chebyshev approximation of the actual squarefree displacement
Source: the user's four-criteria continuation and its elementary energy proof.
The Hilbert error bound is unconditional. Physical averaging bounds on these
approximants are separate open arithmetic obligations.
-/
noncomputable section

namespace RiemannResearch.RH.QSquarefreeChebyshev
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeDisplacementRigidity QSquarefreeSmoothedProjection
open QSquarefreeDisplacementResolvent
open RiemannResearch.Analysis.ChebyshevEnergy

def operator : QHilbert →L[ℝ] QHilbert :=
  (4 : ℝ) • (closure.starProjection.comp (B.comp closure.starProjection)) -
    closure.starProjection

theorem projection_symmetric (x y : QHilbert) :
    inner ℝ (closure.starProjection x) y =
      inner ℝ x (closure.starProjection y) := by
  have h1 := Submodule.inner_right_of_mem_orthogonal
    (closure.starProjection_apply_mem x)
    (Submodule.sub_starProjection_mem_orthogonal (K := closure) y)
  have h2 := Submodule.inner_right_of_mem_orthogonal
    (closure.starProjection_apply_mem y)
    (Submodule.sub_starProjection_mem_orthogonal (K := closure) x)
  rw [inner_sub_right] at h1 h2
  have hc1 := real_inner_comm (closure.starProjection y) x
  have hc2 := real_inner_comm (closure.starProjection y) (closure.starProjection x)
  linarith

theorem operator_symmetric (x y : QHilbert) :
    inner ℝ (operator x) y = inner ℝ x (operator y) := by
  have hb : inner ℝ (closure.starProjection (B (closure.starProjection x))) y =
      inner ℝ x (closure.starProjection (B (closure.starProjection y))) := by
    rw [projection_symmetric, B_symmetric, projection_symmetric]
  change inner ℝ ((4 : ℝ) • closure.starProjection (B (closure.starProjection x)) -
      closure.starProjection x) y =
    inner ℝ x ((4 : ℝ) • closure.starProjection (B (closure.starProjection y)) -
      closure.starProjection y)
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    conj_trivial, hb, projection_symmetric]

theorem operator_eq_feedback (x : QHilbert) :
    operator x = (3 : ℝ) • centeredFeedback (closure.starProjection x) := by
  have hp : closure.starProjection (closure.starProjection x) =
      closure.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (closure.starProjection_apply_mem x)
  change (4 : ℝ) • closure.starProjection (B (closure.starProjection x)) -
      closure.starProjection x = _
  simp only [centeredFeedback, map_sub, map_smul, hp]
  module

theorem operator_contracts (x : QHilbert) : ‖operator x‖ ≤ ‖x‖ := by
  rw [operator_eq_feedback, norm_smul, Real.norm_eq_abs]
  norm_num
  have h := centeredFeedback_norm_le (closure.starProjection x)
  have hp : ‖closure.starProjection x‖ ≤ ‖x‖ := by
    calc
      ‖closure.starProjection x‖ ≤ ‖closure.starProjection‖ * ‖x‖ :=
        closure.starProjection.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le closure) (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  nlinarith

theorem displacement_operator_equation :
    operator displacement = (3 : ℝ) • displacement - (4 : ℝ) • correction := by
  have hp : closure.starProjection displacement = displacement :=
    Submodule.starProjection_eq_self_iff.mpr displacement_mem
  have hb : closure.starProjection (B displacement) = displacement - correction := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact displacement_fixed_point.symm
  change (4 : ℝ) • closure.starProjection (B (closure.starProjection displacement)) -
      closure.starProjection displacement = _
  rw [hp, hb]
  module

def accelerated (n : ℕ) : QHilbert := approximant operator correction n

theorem accelerated_error (n : ℕ) :
    displacement - accelerated n =
      (denominator n)⁻¹ • firstKind operator displacement n :=
  approximant_error operator correction displacement displacement_operator_equation n

theorem accelerated_error_norm_le (n : ℕ) :
    ‖displacement - accelerated n‖ ≤ ‖displacement‖ / denominator n :=
  approximant_error_norm_le operator operator_symmetric operator_contracts
    correction displacement displacement_operator_equation n
end RiemannResearch.RH.QSquarefreeChebyshev
