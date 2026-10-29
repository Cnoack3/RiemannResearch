/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTMovingPredictionGain
import RiemannResearch.RH.QSquarefreeGapHeadCost
import RiemannResearch.RH.QCompensatedResidueGap
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QCRTPredictionBudget
import RiemannResearch.RH.QExactHeadSubpolynomial
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A smaller budget using observed dictionary-gain cancellation

Source: user-provided continuation of a4911d47, 29 October 2026.
The unconditional upper bound uses the positive part of a(2b-a), rather
than b squared, in the gap term. The conditional RH consumer still requires
subpolynomial growth of this explicit new budget; that obligation is Open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTCancellationBudget
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets
open QCRTPeriodHeadBalance QSquarefreeEnergyTransitions QSquarefreeGapHeadCost
open QCRTMovingPredictionGain QSquarefreeHeadStep QCompensatedResidueGap

def signedPrediction (i : ℕ) : ℝ :=
  max 0 (oldMismatch i * (2 * nextMismatch i - oldMismatch i))

theorem signedPrediction_nonneg (i : ℕ) : 0 ≤ signedPrediction i :=
  le_max_left _ _

theorem signedPrediction_le_sq (i : ℕ) : signedPrediction i ≤ nextMismatch i ^ 2 := by
  apply max_le (sq_nonneg _)
  nlinarith [sq_nonneg (nextMismatch i - oldMismatch i)]

theorem dense_net_gap_bound (i : ℕ) :
    headCost denseSchedule i - periodGain denseSchedule i ≤
      signedPrediction i * gapWeight (i + 2) (squarefreeAnchor i) := by
  by_cases hsf : Squarefree (i + 2)
  · have hnL : i + 2 ∣ primorial (denseSchedule (i + 1) + 2) :=
      dvd_trans hsf.dvd_primorial
        (primorial_dvd_primorial (by dsimp [denseSchedule]; omega))
    have hcap : 0 < denseCapacity i :=
      stepCapacity_pos (i + 2) _ _ (by omega) (primorial_pos _)
        hnL (denseAnchor_mem i) (squarefreeAnchor_spec i).1
    have hinv : 1 / denseCapacity i ≤ gapWeight (i + 2) (squarefreeAnchor i) :=
      (inverse_stepCapacity_le_trial_energy (i + 2) _ _ (by omega)
        (primorial_pos _) hnL (denseAnchor_mem i) (squarefreeAnchor_spec i).1).trans
        (compensatedResidue_gap_log_bound (i + 2) _ (by omega)
          (squarefreeAnchor_spec i).1 (squarefreeAnchor_le_two_mul i))
    have hstep := stageEnergy_step denseSchedule denseSchedule_monotone denseSchedule_head i
    have hb := dense_signed_prediction_bound i hsf
    have hprod := div_le_div_of_nonneg_right
      (le_max_right 0 (oldMismatch i * (2 * nextMismatch i - oldMismatch i))) hcap.le
    have hw := mul_le_mul_of_nonneg_left hinv (signedPrediction_nonneg i)
    have heq : signedPrediction i * (1 / denseCapacity i) =
        signedPrediction i / denseCapacity i := by ring
    rw [heq] at hw
    change oldMismatch i * (2 * nextMismatch i - oldMismatch i) / denseCapacity i ≤
      signedPrediction i / denseCapacity i at hprod
    linarith
  · rw [headCost_eq_zero_of_nonsquarefree denseSchedule i (denseSchedule_head (i + 1)) hsf]
    have hg : 0 ≤ periodGain denseSchedule i := sq_nonneg _
    have hw := mul_nonneg (signedPrediction_nonneg i)
      (gapWeight_nonneg (i + 2) _ (by omega) (squarefreeAnchor_spec i).1
        (squarefreeAnchor_le_two_mul i))
    linarith

def cancellationBudget (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, min
    ((4 / zetaTwo) * (nextMismatch i ^ 2 / (i + 1 : ℕ)))
    (signedPrediction i * gapWeight (i + 2) (squarefreeAnchor i))

theorem cancellationBudget_nonneg (N : ℕ) : 0 ≤ cancellationBudget N := by
  apply Finset.sum_nonneg
  intro i _
  apply le_min
  · positivity [zetaTwo_pos]
  · exact mul_nonneg (signedPrediction_nonneg i)
      (gapWeight_nonneg (i + 2) _ (by omega)
        (squarefreeAnchor_spec i).1 (squarefreeAnchor_le_two_mul i))

theorem cancellationBudget_le_gapBudget (N : ℕ) :
    cancellationBudget N ≤ gapBudget N := by
  apply Finset.sum_le_sum
  intro i _
  apply min_le_min le_rfl
  exact mul_le_mul_of_nonneg_right (signedPrediction_le_sq i)
    (gapWeight_nonneg (i + 2) _ (by omega)
      (squarefreeAnchor_spec i).1 (squarefreeAnchor_le_two_mul i))

theorem dense_energy_le_cancellationBudget (N : ℕ) :
    stageEnergy denseSchedule N ≤ stageEnergy denseSchedule 0 + cancellationBudget N := by
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
  · exact dense_net_gap_bound i

open QCRTPredictionBudget Filter
open scoped Topology

theorem trial_error_le_cancellationBudget (N : ℕ) :
    ‖qOne - trial N‖ ^ 2 ≤
      2 + 2 * stageEnergy denseSchedule 0 + 2 * cancellationBudget N := by
  have hnorm := norm_sub_le qOne (trial N)
  rw [qOne_norm] at hnorm
  have he := dense_energy_le_cancellationBudget N
  change ‖trial N‖ ^ 2 ≤ _ at he
  nlinarith [norm_nonneg (qOne - trial N), norm_nonneg (trial N),
    sq_nonneg (‖trial N‖ - 1)]

/-- Conditional research reduction. The actual signed budget growth is Open. -/
theorem riemannHypothesis_of_subpolynomial_cancellationBudget
    (hsub : Tendsto
      (fun N => Real.log (1 + cancellationBudget N) / Real.log ((N + 2 : ℕ) : ℝ))
      atTop (𝓝 0)) : RiemannHypothesis := by
  let E : ℕ → ℝ := fun N => 1 + 2 * stageEnergy denseSchedule 0 + 2 * cancellationBudget N
  let A : ℝ := 4 + 2 * stageEnergy denseSchedule 0
  have he0 : 0 ≤ stageEnergy denseSchedule 0 := sq_nonneg _
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hE : ∀ N, 0 ≤ E N := by
    intro N
    dsimp [E]
    positivity [cancellationBudget_nonneg N]
  have hn : Tendsto (fun N : ℕ => ((N + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hscaled :=
    RiemannResearch.Analysis.SubpolynomialWindow.relativeLog_tendsto_zero_of_scaled_budget
    E cancellationBudget (fun N => ((N + 2 : ℕ) : ℝ)) A hA hE
    cancellationBudget_nonneg hn
    (Eventually.of_forall (fun N => by
      dsimp [A, E]
      nlinarith [cancellationBudget_nonneg N,
        mul_nonneg he0 (cancellationBudget_nonneg N)])) hsub
  apply QExactHeadSubpolynomial.riemannHypothesis_of_cofinal_exact_head_subpolynomial
    trial (fun N => N + 2) E hn trial_legal trial_head hE
  · intro N
    have h := trial_error_le_cancellationBudget N
    dsimp [E]
    linarith
  · exact hscaled

end RiemannResearch.RH.QCRTCancellationBudget
