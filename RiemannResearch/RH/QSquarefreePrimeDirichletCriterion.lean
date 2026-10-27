/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeResamplingPoincare
import RiemannResearch.RH.QCountablePairEnergy
import RiemannResearch.RH.QSquarefreeLogResidualTail
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QPolylogTailEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Actual squarefree correction criterion for the complete prime Dirichlet form

Source: the user-provided PrimeResamplingResearch20261027.md, Sections 4–6.
The complete actual kernel and unconditional gap-one theorem supply all
analytic premises. Finite Dirichlet energy of the weighted limiting correction
is equivalent to zero actual residual, and implies Mathlib's RiemannHypothesis.
Its finiteness remains an Open arithmetic obligation. No converse from RH to
squarefree density is used or asserted.
-/

noncomputable section
open Filter
open scoped BigOperators ENNReal Topology
namespace RiemannResearch.RH.QSquarefreePrimeDirichletCriterion
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeSmoothedProjection
open QCountableJumpEnergy QPairVariance QPrimeResampling PrimeResampling
open QAnnihilatorTailEscape QPolylogTailEnergy QSquarefreeLogResidualTail
open RiemannResearch.Analysis.LogTailWeights
open RiemannResearch.Analysis.CountableJumpEnergy

/-- The exact actual correction form; it may take the value infinity. -/
def correctionDirichletEnergy : ℝ≥0∞ :=
  dirichletEnergy (qWeightedSequence correction)

theorem residual_zero_of_correction_weightedEnergy_summable
    (hs : Summable (polylogWeightedEnergyTerm 2 correction)) :
    limitingResidual = 0 := by
  let T : ℝ := ∑' n, polylogWeightedEnergyTerm 2 correction n
  have hb (N : ℕ) : logWeight 2 N * ‖tail N correction‖ ^ 2 ≤ 64 * T := by
    have h1 := mul_le_mul_of_nonneg_right
      (logWeight_le_polylogTailProfile 2 N) (sq_nonneg ‖tail N correction‖)
    have h2 := mul_le_mul_of_nonneg_left (profile_mul_tail_energy_le 2 N correction hs)
      (by norm_num : (0 : ℝ) ≤ 64)
    norm_num at h1
    dsimp [T]
    nlinarith
  exact (residual_zero_iff_correction_frequently_bounded_log_scaled_tail 2).mpr
    ⟨64 * T, (Eventually.of_forall hb).frequently⟩

/-- Finite actual prime energy supplies square integrability itself; no
independent first- or second-moment hypothesis is required. -/
theorem residual_zero_of_correctionDirichletEnergy_ne_top
    (hD : correctionDirichletEnergy ≠ ⊤) : limitingResidual = 0 := by
  have hs := qSquare_summable_of_energy_ne_top primeFlow (qWeightedSequence correction)
    (prime_resampling_poincare _) hD
  have hw : Summable (polylogWeightedEnergyTerm 2 correction) := by
    simpa only [qWeightedSequence_square_term] using hs
  exact residual_zero_of_correction_weightedEnergy_summable hw

theorem correctionDirichletEnergy_eq_zero_of_residual_zero
    (hr : limitingResidual = 0) : correctionDirichletEnergy = 0 := by
  have hc : correction = 0 := by simp [correction, hr]
  have hq : qSequence (0 : QHilbert) = 0 := qSequenceLinear.map_zero
  simp [correctionDirichletEnergy, dirichletEnergy, countableJumpEnergy,
    qWeightedSequence, hc, hq]

/-- Complete-form finiteness is an exact zero-residual criterion. -/
theorem correctionDirichletEnergy_ne_top_iff_residual_zero :
    correctionDirichletEnergy ≠ ⊤ ↔ limitingResidual = 0 := by
  constructor
  · exact residual_zero_of_correctionDirichletEnergy_ne_top
  · intro hr
    rw [correctionDirichletEnergy_eq_zero_of_residual_zero hr]
    exact ENNReal.zero_ne_top

theorem correctionDirichletEnergy_eq_zero_iff_residual_zero :
    correctionDirichletEnergy = 0 ↔ limitingResidual = 0 := by
  constructor
  · intro h
    apply residual_zero_of_correctionDirichletEnergy_ne_top
    rw [h]
    exact ENNReal.zero_ne_top
  · exact correctionDirichletEnergy_eq_zero_of_residual_zero

/-- The actual weighted limiting correction has energy either zero or infinity. -/
theorem correctionDirichletEnergy_eq_top_iff_residual_ne_zero :
    correctionDirichletEnergy = ⊤ ↔ limitingResidual ≠ 0 := by
  simpa only [not_not] using not_congr correctionDirichletEnergy_ne_top_iff_residual_zero

/-- Conditional research reduction with precisely one remaining arithmetic
premise: finiteness of the displayed actual correction Dirichlet form. -/
theorem riemannHypothesis_of_correctionDirichletEnergy_ne_top
    (hD : correctionDirichletEnergy ≠ ⊤) : RiemannHypothesis := by
  have hr := residual_zero_of_correctionDirichletEnergy_ne_top hD
  have hm : qOne ∈ ZetaTwoOptimizerStage.closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

end RiemannResearch.RH.QSquarefreePrimeDirichletCriterion
