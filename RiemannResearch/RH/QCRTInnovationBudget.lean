/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTInnovationGain
import RiemannResearch.RH.QCRTCancellationBudget
import RiemannResearch.RH.QCRTMovingPredictionGain
import RiemannResearch.RH.QSquarefreeGapHeadCost
import RiemannResearch.RH.QCompensatedResidueGap
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QCRTPredictionBudget
import RiemannResearch.RH.QSquarefreeHeadStep
import RiemannResearch.RH.QExactHeadSubpolynomial
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A smaller actual budget retaining the capacity-increment penalty

Source: continuation of the user-provided moving-prediction cancellation
agenda, 29 October 2026. The extra nonnegative penalty comes from the old
tangent's observation capacity. The unconditional energy bound is stronger;
the conditional RH theorem still requires an Open arithmetic growth provider.
-/

namespace RiemannResearch.RH.QCRTInnovationBudget
noncomputable section
open scoped BigOperators
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets
open QCRTPeriodHeadBalance QSquarefreeEnergyTransitions QSquarefreeGapHeadCost
open QCRTMovingPredictionGain QSquarefreeHeadStep QCompensatedResidueGap
open QCRTInnovationGain QCRTCancellationBudget

def refinedPrediction (i : ℕ) : ℝ :=
  max 0 (oldMismatch i * (2 * nextMismatch i - oldMismatch i) - innovationPenalty i)

theorem refinedPrediction_nonneg (i : ℕ) : 0 ≤ refinedPrediction i :=
  le_max_left _ _

theorem refinedPrediction_le_signedPrediction (i : ℕ) :
    refinedPrediction i ≤ signedPrediction i :=
  max_le_max le_rfl (sub_le_self _ (innovationPenalty_nonneg i))

theorem dense_net_innovation_bound (i : ℕ) :
    headCost denseSchedule i - periodGain denseSchedule i ≤
      refinedPrediction i * gapWeight (i + 2) (squarefreeAnchor i) := by
  by_cases hsf : Squarefree (i + 2)
  · have hnL : i + 2 ∣ primorial (denseSchedule (i + 1) + 2) :=
      dvd_trans hsf.dvd_primorial
        (primorial_dvd_primorial (by dsimp [denseSchedule]; omega))
    have hcap := denseCapacity_pos i hsf
    have hinv : 1 / denseCapacity i ≤ gapWeight (i + 2) (squarefreeAnchor i) :=
      (inverse_stepCapacity_le_trial_energy (i + 2) _ _ (by omega)
        (primorial_pos _) hnL (denseAnchor_mem i) (squarefreeAnchor_spec i).1).trans
        (compensatedResidue_gap_log_bound (i + 2) _ (by omega)
          (squarefreeAnchor_spec i).1 (squarefreeAnchor_le_two_mul i))
    have hstep := stageEnergy_step denseSchedule denseSchedule_monotone denseSchedule_head i
    have hb := dense_refined_signed_transition i hsf
    have hprod := div_le_div_of_nonneg_right
      (le_max_right 0
        (oldMismatch i * (2 * nextMismatch i - oldMismatch i) - innovationPenalty i))
      hcap.le
    have hw := mul_le_mul_of_nonneg_left hinv (refinedPrediction_nonneg i)
    have heq : refinedPrediction i * (1 / denseCapacity i) =
        refinedPrediction i / denseCapacity i := by ring
    rw [heq] at hw
    change (oldMismatch i * (2 * nextMismatch i - oldMismatch i) - innovationPenalty i) /
      denseCapacity i ≤ refinedPrediction i / denseCapacity i at hprod
    linarith [sq_nonneg ‖innovationRemainder i‖]
  · rw [headCost_eq_zero_of_nonsquarefree denseSchedule i (denseSchedule_head (i + 1)) hsf]
    have hg : 0 ≤ periodGain denseSchedule i := sq_nonneg _
    have hw := mul_nonneg (refinedPrediction_nonneg i)
      (gapWeight_nonneg (i + 2) _ (by omega) (squarefreeAnchor_spec i).1
        (squarefreeAnchor_le_two_mul i))
    linarith

def innovationBudget (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, min
    ((4 / zetaTwo) * (nextMismatch i ^ 2 / (i + 1 : ℕ)))
    (refinedPrediction i * gapWeight (i + 2) (squarefreeAnchor i))

theorem innovationBudget_nonneg (N : ℕ) : 0 ≤ innovationBudget N := by
  apply Finset.sum_nonneg
  intro i _
  apply le_min
  · positivity [zetaTwo_pos]
  · exact mul_nonneg (refinedPrediction_nonneg i)
      (gapWeight_nonneg (i + 2) _ (by omega)
        (squarefreeAnchor_spec i).1 (squarefreeAnchor_le_two_mul i))

theorem innovationBudget_le_cancellationBudget (N : ℕ) :
    innovationBudget N ≤ cancellationBudget N := by
  apply Finset.sum_le_sum
  intro i _
  apply min_le_min le_rfl
  exact mul_le_mul_of_nonneg_right (refinedPrediction_le_signedPrediction i)
    (gapWeight_nonneg (i + 2) _ (by omega)
      (squarefreeAnchor_spec i).1 (squarefreeAnchor_le_two_mul i))

theorem dense_energy_le_innovationBudget (N : ℕ) :
    stageEnergy denseSchedule N ≤ stageEnergy denseSchedule 0 + innovationBudget N := by
  rw [stageEnergy_telescope denseSchedule denseSchedule_monotone denseSchedule_head]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  apply le_min
  · have hc := dense_headCost_bound i
    have hg : 0 ≤ periodGain denseSchedule i := sq_nonneg _
    have he : nextMismatch i ^ 2 * ((1 / zetaTwo) * (4 / (i + 1 : ℕ))) =
        (4 / zetaTwo) * (nextMismatch i ^ 2 / (i + 1 : ℕ)) := by ring
    rw [he] at hc
    linarith
  · exact dense_net_innovation_bound i

open QCRTPredictionBudget Filter
open scoped Topology

theorem trial_error_le_innovationBudget (N : ℕ) :
    ‖qOne - trial N‖ ^ 2 ≤
      2 + 2 * stageEnergy denseSchedule 0 + 2 * innovationBudget N := by
  have hnorm := norm_sub_le qOne (trial N)
  rw [qOne_norm] at hnorm
  have he := dense_energy_le_innovationBudget N
  change ‖trial N‖ ^ 2 ≤ _ at he
  nlinarith [norm_nonneg (qOne - trial N), norm_nonneg (trial N),
    sq_nonneg (‖trial N‖ - 1)]

/-- Conditional research reduction: subpolynomial growth of this actual
capacity-increment budget is Open. -/
theorem riemannHypothesis_of_subpolynomial_innovationBudget
    (hsub : Tendsto
      (fun N => Real.log (1 + innovationBudget N) / Real.log ((N + 2 : ℕ) : ℝ))
      atTop (𝓝 0)) : RiemannHypothesis := by
  let E : ℕ → ℝ := fun N => 1 + 2 * stageEnergy denseSchedule 0 + 2 * innovationBudget N
  let A : ℝ := 4 + 2 * stageEnergy denseSchedule 0
  have he0 : 0 ≤ stageEnergy denseSchedule 0 := sq_nonneg _
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hE : ∀ N, 0 ≤ E N := by
    intro N
    dsimp [E]
    positivity [innovationBudget_nonneg N]
  have hn : Tendsto (fun N : ℕ => ((N + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hscaled :=
    RiemannResearch.Analysis.SubpolynomialWindow.relativeLog_tendsto_zero_of_scaled_budget
    E innovationBudget (fun N => ((N + 2 : ℕ) : ℝ)) A hA hE
    innovationBudget_nonneg hn
    (Eventually.of_forall (fun N => by
      dsimp [A, E]
      nlinarith [innovationBudget_nonneg N,
        mul_nonneg he0 (innovationBudget_nonneg N)])) hsub
  apply QExactHeadSubpolynomial.riemannHypothesis_of_cofinal_exact_head_subpolynomial
    trial (fun N => N + 2) E hn trial_legal trial_head hE
  · intro N
    have h := trial_error_le_innovationBudget N
    dsimp [E]
    linarith
  · exact hscaled

end
end RiemannResearch.RH.QCRTInnovationBudget
