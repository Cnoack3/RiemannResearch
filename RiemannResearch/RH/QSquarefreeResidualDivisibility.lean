/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorLegality
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QSquarefreeProjectionLimits
import RiemannResearch.RH.QSquarefreeProjectionSigns
import RiemannResearch.RH.QPrimeResamplingParity
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.QPrimeResampling
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Divisibility moments of the actual squarefree residual

Source: user-provided tensor-product and prime-independence question, November 5, 2026.
The proofs assemble projection orthogonality, the exact identity
qDivisor 2 = qOne - 2 • qResidue 2, and complete Q dilation moments.
The even moment was already used privately in QSquarefreeFirstCoordinate;
this module makes it reusable together with its covariance and dilation consequences.

The zero-covariance and dyadic-invariance hypotheses below are conditional
research reductions. Neither follows from independence of the input prime valuations.
The identities have no unproved arithmetic hypotheses.
-/
noncomputable section
namespace RiemannResearch.RH.QSquarefreeResidualDivisibility
open ZetaTwoHilbert ZetaTwoOptimizerStage QDivisibilityDensity
open QDivisorLegality QSquarefreeProjectionLimits QSquarefreeProjectionSigns QPrimeResampling
open ZetaTwoProbability

theorem residual_inner_g2 : inner ℝ limitingResidual (qResidue 2) = 0 := by
  rw [real_inner_comm]
  exact (closure.mem_orthogonal limitingResidual).mp limitingResidual_mem_orthogonal
    _ (prime_atom_mem_closure 2 Nat.prime_two)

theorem residual_odd_moment :
    inner ℝ limitingResidual ((2 : ℝ) • qResidue 2) = 0 := by
  rw [inner_smul_right, residual_inner_g2, mul_zero]

theorem residual_even_moment :
    inner ℝ limitingResidual (qDivisor 2) = ‖limitingResidual‖ ^ 2 := by
  rw [qDivisor_two_eq, inner_sub_right, inner_smul_right,
    residual_inner_g2, mul_zero, sub_zero]
  exact limitingResidual_mean_eq_energy

theorem residual_even_covariance :
    inner ℝ limitingResidual (qDivisor 2) -
      inner ℝ limitingResidual qOne * inner ℝ qOne (qDivisor 2) =
    (3 / 4 : ℝ) * ‖limitingResidual‖ ^ 2 := by
  rw [residual_even_moment, limitingResidual_mean_eq_energy,
    qOne_inner_qDivisor 2 (by norm_num)]
  ring

theorem residual_zero_of_parity_uncorrelated
    (h : inner ℝ limitingResidual (qDivisor 2) -
      inner ℝ limitingResidual qOne * inner ℝ qOne (qDivisor 2) = 0) :
    limitingResidual = 0 := by
  rw [residual_even_covariance] at h
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg limitingResidual]

theorem residual_dyadic_dilation_mean :
    inversePowerMean 0 (fun n => qSequence limitingResidual (2 * n)) =
      4 * ‖limitingResidual‖ ^ 2 := by
  have h := inner_qDivisor_eq_dilation limitingResidual 2 (by norm_num)
  rw [residual_even_moment] at h
  norm_num at h
  linarith

theorem residual_zero_of_dyadic_invariant
    (h : C 2 limitingResidual = limitingResidual) :
    limitingResidual = 0 := by
  have he := C_selfAdjoint 2 limitingResidual (qResidue 2)
  rw [h, C_two_qResidue_two, inner_smul_right,
    residual_inner_g2, limitingResidual_mean_eq_energy] at he
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg limitingResidual]

/-- OPEN arithmetic premise: invariance along every dyadic scaling orbit. -/
theorem residual_zero_of_dyadic_scaling
    (h : ∀ n, qSequence limitingResidual (2 * n) = qSequence limitingResidual n) :
    limitingResidual = 0 := by
  apply residual_zero_of_dyadic_invariant
  exact (C_eq_self_iff 2 limitingResidual).mpr h

#print axioms residual_even_moment
#print axioms residual_even_covariance
#print axioms residual_dyadic_dilation_mean
#print axioms residual_zero_of_dyadic_invariant
end RiemannResearch.RH.QSquarefreeResidualDivisibility
