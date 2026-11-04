/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeDisplacementEnergy
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeBoundary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact Schur-witness energies without an inverse operator

Source: the user-provided `Pasted text(9).txt`, final paper, section 5,
November 4, 2026. The existing normal equation yields both Schur energy
identities directly. The two exact remainders below retain the complete
displacement square and support stronger inequalities for the actual target.
They do not establish the open physical-regularity estimate needed for RH.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeSchurWitness
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeDisplacementRigidity QSquarefreeDisplacementEnergy
open QSquarefreeBoundary

theorem witness_mean_eq_residual_inner :
    inner ℝ qOne witness = inner ℝ limitingResidual witness := by
  have h := Submodule.inner_right_of_mem_orthogonal
    (closure.starProjection_apply_mem qOne) witness_mem_orthogonal
  change inner ℝ qOne witness =
    inner ℝ (qOne - closure.starProjection qOne) witness
  rw [inner_sub_left, h, sub_zero]

/-- First exact Schur form: the correction contributes its full metric energy. -/
theorem witness_mean_q_energy :
    inner ℝ qOne witness = inner ℝ limitingResidual (B limitingResidual) +
      ‖displacement‖ ^ 2 - inner ℝ displacement (B displacement) := by
  have hnormal := displacement_normal
  rw [map_add, inner_add_right] at hnormal
  have hrd : inner ℝ limitingResidual displacement = 0 := by
    rw [real_inner_comm]
    exact residual_displacement_orthogonal
  have hsym : inner ℝ limitingResidual (B displacement) =
      inner ℝ displacement (B limitingResidual) := by
    rw [← B_symmetric, real_inner_comm]
  rw [witness_mean_eq_residual_inner, witness, pResidual_eq_residual_add_displacement,
    map_add, inner_sub_right, inner_add_right, hrd, sub_zero, hsym]
  linarith

/-- Second exact Schur form: the total B energy minus the legal response square. -/
theorem witness_mean_total_energy :
    inner ℝ qOne witness =
      inner ℝ pResidual (B pResidual) - ‖displacement‖ ^ 2 := by
  have hnormal := displacement_normal
  rw [map_add, inner_add_right] at hnormal
  have hsym : inner ℝ limitingResidual (B displacement) =
      inner ℝ displacement (B limitingResidual) := by
    rw [← B_symmetric, real_inner_comm]
  rw [witness_mean_q_energy, pResidual_eq_residual_add_displacement,
    map_add, inner_add_left, inner_add_right, inner_add_right, hsym]
  linarith

theorem pResidual_norm_sq :
    ‖pResidual‖ ^ 2 = ‖limitingResidual‖ ^ 2 + ‖displacement‖ ^ 2 := by
  rw [pResidual_eq_residual_add_displacement, norm_add_sq_real,
    real_inner_comm, residual_displacement_orthogonal]
  ring

/-- Exact lower-form remainder; no positive term is discarded. -/
theorem witness_mean_lower_remainder (a : ℝ) :
    inner ℝ qOne witness -
      (inner ℝ limitingResidual (B limitingResidual) + (1-a)*‖displacement‖^2) =
      a*‖displacement‖^2 - inner ℝ displacement (B displacement) := by
  rw [witness_mean_q_energy]
  ring

/-- Exact upper-form remainder, including the signed displacement correction. -/
theorem witness_mean_upper_remainder (a : ℝ) :
    a*‖limitingResidual‖^2 - (1-a)*‖displacement‖^2 - inner ℝ qOne witness =
      a*‖pResidual‖^2 - inner ℝ pResidual (B pResidual) := by
  rw [witness_mean_total_energy, pResidual_norm_sq]
  ring

theorem pResidual_fourSite : fourSiteFunctional pResidual = 0 := by
  rw [pResidual_eq_residual_add_displacement, map_add,
    residual_fourSite, displacement_fourSite, add_zero]

/-- The actual target satisfies the same four-site constraint as legal vectors,
so both sides improve on the generic Schur-complement half-identity bound. -/
theorem witness_mean_bounds :
    inner ℝ limitingResidual (B limitingResidual) +
        (1017/2000 : ℝ)*‖displacement‖^2 ≤ inner ℝ qOne witness ∧
      inner ℝ qOne witness ≤ (983/2000 : ℝ)*‖limitingResidual‖^2 -
        (1017/2000 : ℝ)*‖displacement‖^2 := by
  have hd := B_inner_le_four_site_983_2000 displacement_fourSite
  have hp := B_inner_le_four_site_983_2000 pResidual_fourSite
  have hlo := witness_mean_lower_remainder (983/2000)
  have hhi := witness_mean_upper_remainder (983/2000)
  constructor <;> linarith

/-- Faithfulness is attached to this concrete quadratic form, not to an
arbitrary vector state on the joint C-star algebra. -/
theorem witness_mean_pos_iff :
    0 < inner ℝ qOne witness ↔ limitingResidual ≠ 0 := by
  constructor
  · intro hp hr
    have hd := displacement_eq_zero_of_residual_eq_zero hr
    rw [witness_mean_q_energy, hr, hd] at hp
    simp at hp
  · intro hr
    have hp : 0 < inner ℝ limitingResidual (B limitingResidual) :=
      lt_of_le_of_ne (B_positive _)
        (Ne.symm (fun h => hr (B_faithful _ h)))
    have hlo := witness_mean_bounds.1
    nlinarith [sq_nonneg ‖displacement‖]

end RiemannResearch.RH.QSquarefreeSchurWitness
