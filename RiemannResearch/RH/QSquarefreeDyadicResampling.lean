/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeProjectionSharpness
import RiemannResearch.RH.QPrimeResamplingParity
import RiemannResearch.RH.QPrimeResampling
import RiemannResearch.RH.QParityConditionalTarget
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.Analysis.ProjectionAveragingDefect
import Mathlib.Tactic.NormNum

/-!
# Actual dyadic detection of the squarefree residual

Source: independently derived continuation of the user's
PrimeResamplingFormalization20261027.md. All averaging identities here concern
the actual Q law. Both exact norm-square remainders are retained. Invariance
of the limiting residual under multiplication by two remains an Open arithmetic
obligation; the conditional RH consumer does not assert that invariance.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeDyadicResampling
open ZetaTwoHilbert ZetaTwoOptimizerStage QPrimeResampling
open RiemannResearch.Analysis.ProjectionAveragingDefect

/-- Actual prime-two resampling defect of the limiting projection residual. -/
def limitingDefect : QHilbert := limitingResidual - C 2 limitingResidual

theorem limiting_defect_pairing :
    inner ℝ limitingDefect dyadicCenteredAtom = -(3 / 8 : ℝ) * ‖limitingResidual‖ ^ 2 := by
  have havg : (primeInvariant 2).starProjection (qResidue 2) =
      (3 / 8 : ℝ) • qOne := C_two_qResidue_two
  simpa only [limitingDefect, limitingResidual, dyadicCenteredAtom, C, havg] using
    defect_pairing closure (primeInvariant 2) qOne (qResidue 2) (3 / 8)
      QParityConditionalTarget.qResidue_two_mem_closure C_two_qResidue_two

/-- Exact nonnegative remainder for actual dyadic resampling. -/
theorem limiting_defect_energy_exact :
    ‖limitingDefect‖ ^ 2 = 3 * (‖limitingResidual‖ ^ 2) ^ 2 +
      ‖limitingDefect + (8 * ‖limitingResidual‖ ^ 2) • dyadicCenteredAtom‖ ^ 2 := by
  have he : ‖qResidue 2 - (primeInvariant 2).starProjection (qResidue 2)‖ ^ 2 =
      (3 / 64 : ℝ) := by
    change ‖qResidue 2 - C 2 (qResidue 2)‖ ^ 2 = _
    rw [C_two_qResidue_two]
    exact dyadicCenteredAtom_norm_sq
  have havg : (primeInvariant 2).starProjection (qResidue 2) =
      (3 / 8 : ℝ) • qOne := C_two_qResidue_two
  simpa only [limitingDefect, limitingResidual, dyadicCenteredAtom, C, havg] using
    parity_defect_energy_exact closure (primeInvariant 2) qOne (qResidue 2)
      QParityConditionalTarget.qResidue_two_mem_closure C_two_qResidue_two he

/-- Complete residual energy with both norm-square remainders retained. -/
theorem limiting_residual_energy_exact :
    ‖limitingResidual‖ ^ 2 = 4 * (‖limitingResidual‖ ^ 2) ^ 2 +
      ‖limitingDefect + (8 * ‖limitingResidual‖ ^ 2) • dyadicCenteredAtom‖ ^ 2 +
      ‖C 2 limitingResidual - (‖limitingResidual‖ ^ 2) • qOne‖ ^ 2 := by
  have he : ‖qResidue 2 - (primeInvariant 2).starProjection (qResidue 2)‖ ^ 2 =
      (3 / 64 : ℝ) := by
    change ‖qResidue 2 - C 2 (qResidue 2)‖ ^ 2 = _
    rw [C_two_qResidue_two]
    exact dyadicCenteredAtom_norm_sq
  have havg : (primeInvariant 2).starProjection (qResidue 2) =
      (3 / 8 : ℝ) • qOne := C_two_qResidue_two
  simpa only [limitingDefect, limitingResidual, dyadicCenteredAtom, C, havg] using
    parity_residual_energy_exact closure (primeInvariant 2) qOne (qResidue 2)
      qOne_norm_sq (qOne_mem_primeInvariant 2 (by norm_num))
      QParityConditionalTarget.qResidue_two_mem_closure C_two_qResidue_two he

theorem limiting_defect_energy_lower :
    3 * (‖limitingResidual‖ ^ 2) ^ 2 ≤ ‖limitingDefect‖ ^ 2 := by
  rw [limiting_defect_energy_exact]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem limiting_defect_zero_iff_residual_zero : limitingDefect = 0 ↔ limitingResidual = 0 := by
  have ht := defect_zero_iff_target_mem closure (primeInvariant 2) qOne (qResidue 2)
    (3 / 8) (by norm_num) QParityConditionalTarget.qResidue_two_mem_closure
    C_two_qResidue_two
  change limitingDefect = 0 ↔ qOne ∈ closure at ht
  rw [ht]
  exact ⟨fun hm => sub_eq_zero.mpr (Submodule.starProjection_eq_self_iff.mpr hm).symm,
    fun hr => Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm⟩

theorem limiting_dilation_invariant_iff_residual_zero :
    (∀ n : ℕ, qSequence limitingResidual (2 * n) = qSequence limitingResidual n) ↔
      limitingResidual = 0 := by
  rw [← mem_primeInvariant, ← C_eq_self_iff]
  rw [← limiting_defect_zero_iff_residual_zero]
  change C 2 limitingResidual = limitingResidual ↔
    limitingResidual - C 2 limitingResidual = 0
  rw [sub_eq_zero]
  exact eq_comm

theorem riemannHypothesis_of_limiting_dilation_invariant
    (h : ∀ n : ℕ, qSequence limitingResidual (2 * n) = qSequence limitingResidual n) :
    RiemannHypothesis := by
  have hr := limiting_dilation_invariant_iff_residual_zero.mp h
  have hm : qOne ∈ closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

def stageDefect (N : ℕ) : QHilbert := residual N - C 2 (residual N)

theorem stageDefect_tendsto : Tendsto stageDefect atTop (𝓝 limitingDefect) :=
  residual_tendsto.sub ((C 2).continuous.tendsto limitingResidual |>.comp residual_tendsto)

theorem stageDefect_tendsto_zero_iff :
    Tendsto stageDefect atTop (𝓝 0) ↔ limitingResidual = 0 := by
  constructor
  · intro h
    exact limiting_defect_zero_iff_residual_zero.mp (tendsto_nhds_unique stageDefect_tendsto h)
  · intro h
    simpa only [limiting_defect_zero_iff_residual_zero.mpr h] using stageDefect_tendsto

end RiemannResearch.RH.QSquarefreeDyadicResampling
