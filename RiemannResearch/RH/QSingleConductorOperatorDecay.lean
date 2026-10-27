/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QConductorDecay
import RiemannResearch.RH.QBoundedSubspaceEvaluation
import RiemannResearch.RH.QBoundedResidueProjection
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QSingleConductorPrerequisites
import RiemannResearch.Analysis.SingleDirectionResponseDifference
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Vanishing smoothed residual-direction ratio

Source: user-provided argument in `SingleConductorProjectionBound.md`;
the decay estimates yield an additional operator-norm consequence.

The new direction obtained by orthogonalizing a large conductor against a
fixed bounded physical space has vanishing smoothed-norm / norm ratio. This
is the scalar input for operator-norm convergence of the off-diagonal block
P_W B (I-P_W) as one conductor is adjoined.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSingleConductorOperatorDecay
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QSingleConductorPrerequisites QBoundedSubspaceEvaluation QBoundedResidueProjection
open RiemannResearch.Analysis.SingleDirectionProjection

/-- Smoothing annihilates the residualized atoms on their natural scale. -/
theorem sqrt_mul_B_residue_residual_norm_tendsto_zero
    (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u : QHilbert, u ∈ U →
      ∀ n : ℕ, |qSequence u n| ≤ C * ‖u‖) :
    Tendsto (fun d : ℕ => Real.sqrt (d : ℝ) *
      ‖B (qResidue d - U.starProjection (qResidue d))‖) atTop (𝓝 0) := by
  have hg : Tendsto (fun d : ℕ => Real.sqrt (d : ℝ) * ‖B (qResidue d)‖)
      atTop (𝓝 0) := by
    simpa only [normalizedConductor, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using B_normalizedConductor_norm_tendsto_zero
  have hp := sqrt_mul_qResidue_projection_norm_tendsto_zero U C hC hbound
  have hmajor := hg.add hp
  simp only [zero_add] at hmajor
  apply squeeze_zero' (Eventually.of_forall (fun d =>
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))) _ hmajor
  apply Eventually.of_forall
  intro d
  rw [map_sub]
  calc
    _ ≤ Real.sqrt (d : ℝ) *
        (‖B (qResidue d)‖ + ‖B (U.starProjection (qResidue d))‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (d : ℝ) *
        (‖B (qResidue d)‖ + ‖U.starProjection (qResidue d)‖) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (B_norm_le _))
        (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- The scalar error multiplier in the one-direction operator comparison
vanishes, uniformly over Hilbert-space inputs. -/
theorem twice_B_residue_residual_norm_div_norm_tendsto_zero
    (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u : QHilbert, u ∈ U →
      ∀ n : ℕ, |qSequence u n| ≤ C * ‖u‖) :
    Tendsto (fun d : ℕ =>
      2 * ‖B (qResidue d - U.starProjection (qResidue d))‖ /
        ‖qResidue d - U.starProjection (qResidue d)‖) atTop (𝓝 0) := by
  have hzeta := zetaTwo_pos
  have hmajor := (sqrt_mul_B_residue_residual_norm_tendsto_zero U C hC hbound).const_mul
    (4 * Real.sqrt zetaTwo)
  simp only [mul_zero] at hmajor
  apply squeeze_zero' (Eventually.of_forall (fun d => by positivity)) _ hmajor
  filter_upwards [eventually_residue_residual_norm_sq_lower U C hC hbound] with d hd
  obtain ⟨hd, hG⟩ := hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hzden : 0 < 4 * zetaTwo * (d : ℝ) := by positivity
  have hscaled : 1 ≤ ‖qResidue d - U.starProjection (qResidue d)‖ ^ 2 *
      (4 * zetaTwo * (d : ℝ)) := (div_le_iff₀ hzden).mp hG
  have hnormpos : 0 < ‖qResidue d - U.starProjection (qResidue d)‖ := by
    have hs : 0 < ‖qResidue d - U.starProjection (qResidue d)‖ ^ 2 :=
      lt_of_lt_of_le (by positivity) hG
    nlinarith [norm_nonneg (qResidue d - U.starProjection (qResidue d))]
  have hunit : 1 ≤ 2 * Real.sqrt zetaTwo * Real.sqrt (d : ℝ) *
      ‖qResidue d - U.starProjection (qResidue d)‖ := by
    have he : (2 * Real.sqrt zetaTwo * Real.sqrt (d : ℝ) *
        ‖qResidue d - U.starProjection (qResidue d)‖) ^ 2 =
        ‖qResidue d - U.starProjection (qResidue d)‖ ^ 2 *
          (4 * zetaTwo * (d : ℝ)) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d),
        Real.sq_sqrt zetaTwo_pos.le]
      ring
    have hnonneg : 0 ≤ 2 * Real.sqrt zetaTwo * Real.sqrt (d : ℝ) *
        ‖qResidue d - U.starProjection (qResidue d)‖ := by positivity
    nlinarith
  apply (div_le_iff₀ hnormpos).mpr
  have hm := mul_le_mul_of_nonneg_left hunit
    (by positivity : 0 ≤ 2 * ‖B (qResidue d - U.starProjection (qResidue d))‖)
  nlinarith

/-- Adjoining a conductor tending to infinity changes the smoothed-residual
response by an operator whose norm tends to zero. The fixed low-dimensional
space is allowed to be any space of bounded physical sequences. -/
theorem response_extension_operator_norm_tendsto_zero
    (U : Submodule ℝ QHilbert) [FiniteDimensional ℝ U]
    (hbounded : ∀ u : QHilbert, u ∈ U →
      ∃ C : ℝ, ∀ n : ℕ, |qSequence u n| ≤ C) :
    Tendsto (fun d : ℕ =>
      ‖responseOperator (U ⊔ Submodule.span ℝ ({qResidue d} : Set QHilbert)) B -
        responseOperator U B‖) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_physical_bound U hbounded
  apply squeeze_zero' (Eventually.of_forall (fun d => norm_nonneg _)) _
    (twice_B_residue_residual_norm_div_norm_tendsto_zero U C hC hbound)
  filter_upwards [eventually_residue_residual_norm_sq_lower U C hC hbound] with d hd
  obtain ⟨hd, hG⟩ := hd
  have hzeta := zetaTwo_pos
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hnonzero : qResidue d - U.starProjection (qResidue d) ≠ 0 := by
    intro he
    rw [he, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hG
    have hpos : 0 < 1 / (4 * zetaTwo * (d : ℝ)) := by positivity
    linarith
  exact response_extension_operator_norm_le U (qResidue d) B B_symmetric hnonzero

/-- In particular, the operator-norm limit holds over every actual fixed
canonical squarefree stage, with no additional boundedness assumption. -/
theorem stage_response_extension_operator_norm_tendsto_zero (N : ℕ) :
    Tendsto (fun d : ℕ =>
      ‖responseOperator (ZetaTwoOptimizerStage.stage N ⊔
          Submodule.span ℝ ({qResidue d} : Set QHilbert)) B -
        responseOperator (ZetaTwoOptimizerStage.stage N) B‖) atTop (𝓝 0) :=
  response_extension_operator_norm_tendsto_zero
    (ZetaTwoOptimizerStage.stage N) (stage_physical_bounded N)

end RiemannResearch.RH.QSingleConductorOperatorDecay
