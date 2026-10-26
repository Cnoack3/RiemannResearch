/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QReciprocalWeightedEnergy
import RiemannResearch.RH.QHeadCrossMoments
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.QHeadTailLayerEnergy
import RiemannResearch.RH.QPolylogMovingHeadEnergy
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QShiftedReciprocalTail
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QTriangularCharge
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unconditional source and negative cumulative-moment budgets

Source: the user's missing actual squarefree bound request, 26 October 2026.
The raw source has a small complete weighted budget and quadratically decaying
tails. These control the negative cumulative moments. The upper bound on their
positive part remains an Open arithmetic obligation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeRawSourceBounds
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QAnnihilatorTailEscape QHeadCrossMoments QPolylogTailEnergy
open QSquarefreeSmoothedProjection

theorem raw_source_weightedEnergy_le (N : ℕ) :
    (∑' n : ℕ, polylogWeightedEnergyTerm 2 (B (residual N)) n) ≤ (1 / 256 : ℝ) := by
  have h := reciprocal_weightedEnergy_le (residual N)
  have hn := QTriangularCharge.residual_norm_le_one N
  nlinarith [norm_nonneg (residual N)]

theorem raw_source_tail_energy_le (N H : ℕ) :
    ‖tail H (B (residual N))‖ ^ 2 ≤ 1 / ((H : ℝ) + 2) ^ 2 := by
  have h := reciprocal_tail_energy_le (residual N) H
  have hn := QTriangularCharge.residual_norm_le_one N
  have hsq : ‖residual N‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (residual N)]
  exact h.trans (div_le_div_of_nonneg_right hsq (by positivity))

theorem raw_remainder_orthogonal (N : ℕ) :
    inner ℝ (movingCorrection N) (B (residual N) - movingCorrection N) = 0 := by
  exact Submodule.inner_right_of_mem_orthogonal
    ((stage N).starProjection_apply_mem (B (residual N)))
    (Submodule.sub_starProjection_mem_orthogonal (K := stage N) (B (residual N)))

/-- Stronger than the generic bounded-source 1/H estimate: the original raw
source gives a 1/H² lower bound, while retaining the actual residual energy. -/
theorem raw_headCross_lower (N H : ℕ) :
    -(‖residual N‖ ^ 2 / (4 * ((H : ℝ) + 2) ^ 2)) ≤
      headCross H (movingCorrection N) (B (residual N) - movingCorrection N) := by
  have hl := headCross_lower H (movingCorrection N) (B (residual N))
    (raw_remainder_orthogonal N)
  have ht := reciprocal_tail_energy_le (residual N) H
  have he : ‖residual N‖ ^ 2 / (4 * ((H : ℝ) + 2) ^ 2) =
      (‖residual N‖ ^ 2 / ((H : ℝ) + 2) ^ 2) / 4 := by rw [div_div, mul_comm (4 : ℝ)]
  rw [he]
  linarith

theorem raw_headCross_lower_uniform (N H : ℕ) :
    -(1 / (4 * ((H : ℝ) + 2) ^ 2)) ≤
      headCross H (movingCorrection N) (B (residual N) - movingCorrection N) := by
  have hl := headCross_lower H (movingCorrection N) (B (residual N))
    (raw_remainder_orthogonal N)
  have ht := raw_source_tail_energy_le N H
  have he : (1 : ℝ) / (4 * ((H : ℝ) + 2) ^ 2) =
      (1 / ((H : ℝ) + 2) ^ 2) / 4 := by rw [div_div, mul_comm (4 : ℝ)]
  rw [he]
  linarith

/-- Uniformly bounded negative variation. The positive-variation upper bound
required to control the actual correction remains Open. -/
theorem raw_negativeCrossVariation_le (N H : ℕ) :
    negativeCrossVariation 2 H (movingCorrection N)
      (B (residual N) - movingCorrection N) ≤ ‖residual N‖ ^ 2 / 1024 := by
  have h := negativeCrossVariation_le_source_total 2 H (movingCorrection N)
    (B (residual N)) (raw_remainder_orthogonal N)
    (reciprocal_weightedEnergy_summable (residual N))
  have hs := reciprocal_weightedEnergy_le (residual N)
  linarith

theorem raw_negativeCrossVariation_le_uniform (N H : ℕ) :
    negativeCrossVariation 2 H (movingCorrection N)
      (B (residual N) - movingCorrection N) ≤ (1 / 1024 : ℝ) := by
  have h := raw_negativeCrossVariation_le N H
  have hn := QTriangularCharge.residual_norm_le_one N
  nlinarith [norm_nonneg (residual N)]

/-- The exact signed tail identity gives a small source remainder in the actual
energy estimate; the positive cumulative budget is deliberately retained. -/
theorem moving_energy_le_raw_positive_variation (N H : ℕ) :
    weightedHeadEnergy 2 H (movingCorrection N) ≤
      2 * positiveCrossVariation 2 H (movingCorrection N)
        (B (residual N) - movingCorrection N) + ‖residual N‖ ^ 2 / 256 := by
  have h := weightedHeadEnergy_le_positive_variation_add_source_total 2 H
    (movingCorrection N) (B (residual N)) (raw_remainder_orthogonal N)
    (reciprocal_weightedEnergy_summable (residual N))
  have hs := reciprocal_weightedEnergy_le (residual N)
  linarith

end RiemannResearch.RH.QSquarefreeRawSourceBounds
