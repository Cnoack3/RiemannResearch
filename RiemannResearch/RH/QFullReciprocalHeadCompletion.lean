/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QHeadResidualCompletion
import RiemannResearch.RH.QFullReciprocalHeadTail
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QShiftedReciprocal

/-!
# Exact complete norm of a reciprocal-head repair

Source: the user's quantitative reciprocal-head request, 7 November 2026.
The reciprocal multiplier R is implemented by QShiftedReciprocal.B; it is
distinct from the density dQ/dP denoted B in the user's current notation.
This is an application of coordinate-head residual completion. It retains
the complete nonnegative remainder and requires no vanishing residual.
The saved module is subject to the repository server verification gate.
-/

noncomputable section
namespace RiemannResearch.RH.QFullReciprocalHeadCompletion
open ZetaTwoHilbert QFiniteSupportDualCriterion QFullResidueProjection
open QFullDisplacement QShiftedReciprocal QFullReciprocalHeadTail

/-- Exact equality, including the norm-square remainder, for the actual target. -/
theorem reciprocal_head_norm_completion (N : ℕ) (F : QHilbert)
    (hF : F ∈ closure) (hh : ∀ n < N, F n = QShiftedReciprocal.B displacement n)
    (ht : ‖qResidual - finiteHead N qResidual‖ ^ 2 ≠ 0) :
    let h := finiteHead N (QShiftedReciprocal.B displacement)
    let t := qResidual - finiteHead N qResidual
    let a := inner ℝ qResidual h
    ‖F‖ ^ 2 = ‖h‖ ^ 2 + a ^ 2 / ‖t‖ ^ 2 +
      ‖F - h + (a / ‖t‖ ^ 2) • t‖ ^ 2 := by
  apply matching_head_residual_completion N (QShiftedReciprocal.B displacement) F qResidual _ hh ht
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal hF qResidual_mem_orthogonal

/-- A sharper energy lower bound with the exact signed head numerator. -/
theorem reciprocal_head_energy_lower (N : ℕ) (F : QHilbert)
    (hF : F ∈ closure) (hh : ∀ n < N, F n = QShiftedReciprocal.B displacement n)
    (ht : ‖qResidual - finiteHead N qResidual‖ ^ 2 ≠ 0) :
    ‖finiteHead N (QShiftedReciprocal.B displacement)‖ ^ 2 +
      (inner ℝ qResidual (finiteHead N (QShiftedReciprocal.B displacement))) ^ 2 /
        ‖qResidual - finiteHead N qResidual‖ ^ 2 ≤ ‖F‖ ^ 2 := by
  apply matching_head_energy_lower N (QShiftedReciprocal.B displacement) F qResidual _ hh ht
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal hF qResidual_mem_orthogonal

/-- This bound remains meaningful even when the residual tail vanishes. -/
theorem reciprocal_head_pairing_bound (N : ℕ) (F : QHilbert)
    (hF : F ∈ closure) (hh : ∀ n < N, F n = QShiftedReciprocal.B displacement n) :
    |inner ℝ qResidual (finiteHead N (QShiftedReciprocal.B displacement))| ≤
      ‖F - finiteHead N (QShiftedReciprocal.B displacement)‖ *
        ‖qResidual - finiteHead N qResidual‖ := by
  apply matching_head_pairing_bound N (QShiftedReciprocal.B displacement) F qResidual _ hh
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal hF qResidual_mem_orthogonal

end RiemannResearch.RH.QFullReciprocalHeadCompletion
