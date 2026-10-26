/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeCRTResponse
import RiemannResearch.RH.QSquarefreeMovingHeadEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Signed CRT remainder criteria for squarefree target closure

Source: the user's infinite-CRT weighted-energy handoff, 26 October 2026,
Sections 6.1--6.3. These are exact reformulations and conditional research
reductions. Their cofinal lower-bound/absorption providers remain Open.
No conductor-divisibility premise is needed for these algebraic implications:
that premise is needed only when using the ordinary Q orthogonality of the
conditioned remainder. No weighted orthogonality is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeCRTCrossCriterion
open ZetaTwoHilbert ZetaTwoProbability QReciprocalConditioning
open QPolylogTailEnergy QSquarefreeCRTResponse QSquarefreeSmoothedProjection

def sourceBudget : ℝ :=
  ∑' n : ℕ, 1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2)

def signedRemainder (N L H : ℕ) (hL : 0 < L) : ℝ :=
  weightedHeadEnergy 2 H (conditionedRemainder N L hL) +
    2 * weightedHeadCross 2 H (movingCorrection N) (conditionedRemainder N L hL)

private theorem energy_nonneg (k H : ℕ) (f : QHilbert) :
    0 ≤ weightedHeadEnergy k H f := by
  exact Finset.sum_nonneg (fun n _ => polylogWeightedEnergyTerm_nonneg k f n)

theorem signedRemainder_exact (N L H : ℕ) (hL : 0 < L) :
    signedRemainder N L H hL =
      weightedHeadEnergy 2 H
        (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N)) -
      weightedHeadEnergy 2 H (movingCorrection N) := by
  have he := conditioned_source_weighted_energy_exact 2 N L H hL
  unfold signedRemainder
  linarith

theorem energy_le_of_signedRemainder_lower (N L H : ℕ) (hL : 0 < L)
    (A : ℝ) (hA : -A ≤ signedRemainder N L H hL) :
    weightedHeadEnergy 2 H (movingCorrection N) ≤ sourceBudget + A := by
  have hs := conditionalReciprocal_residual_head_energy_le L hL N H
  have he := signedRemainder_exact N L H hL
  change _ ≤ sourceBudget at hs
  linarith

theorem signedRemainder_lower_of_energy_le (N L H : ℕ) (hL : 0 < L)
    (C : ℝ) (hC : weightedHeadEnergy 2 H (movingCorrection N) ≤ C) :
    -C ≤ signedRemainder N L H hL := by
  rw [signedRemainder_exact]
  have hs := energy_nonneg 2 H
    (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N))
  linarith

theorem energy_le_of_cross_lower (N L H : ℕ) (hL : 0 < L)
    (A : ℝ) (hA : -A ≤
      weightedHeadCross 2 H (movingCorrection N) (conditionedRemainder N L hL)) :
    weightedHeadEnergy 2 H (movingCorrection N) ≤ sourceBudget + 2*A := by
  apply energy_le_of_signedRemainder_lower N L H hL (2*A)
  have ht := energy_nonneg 2 H (conditionedRemainder N L hL)
  unfold signedRemainder
  linarith

theorem remainder_energy_le (N L H : ℕ) (hL : 0 < L) :
    weightedHeadEnergy 2 H (conditionedRemainder N L hL) ≤
      2*sourceBudget + 2*weightedHeadEnergy 2 H (movingCorrection N) := by
  have h := weightedHeadEnergy_add_le 2 H
    (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N))
    (-movingCorrection N)
  rw [weightedHeadEnergy_neg] at h
  change weightedHeadEnergy 2 H (conditionedRemainder N L hL) ≤ _ at h
  have hs := conditionalReciprocal_residual_head_energy_le L hL N H
  change _ ≤ sourceBudget at hs
  linarith

theorem cross_lower_of_energy_le (N L H : ℕ) (hL : 0 < L)
    (C : ℝ) (hC : weightedHeadEnergy 2 H (movingCorrection N) ≤ C) :
    -(sourceBudget + 2*C) ≤
      weightedHeadCross 2 H (movingCorrection N) (conditionedRemainder N L hL) := by
  have ht := remainder_energy_le N L H hL
  have he := conditioned_source_weighted_energy_exact 2 N L H hL
  have hs := energy_nonneg 2 H
    (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N))
  have hx := energy_nonneg 2 H (movingCorrection N)
  linarith

theorem energy_le_of_absorption (N L H : ℕ) (hL : 0 < L)
    (θ A : ℝ) (hθ : θ < 1)
    (habs : -2 * weightedHeadCross 2 H
      (movingCorrection N) (conditionedRemainder N L hL) ≤
        θ * weightedHeadEnergy 2 H (movingCorrection N) +
          weightedHeadEnergy 2 H (conditionedRemainder N L hL) + A) :
    weightedHeadEnergy 2 H (movingCorrection N) ≤
      (sourceBudget + A) / (1-θ) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-θ)).2
  have he := conditioned_source_weighted_energy_exact 2 N L H hL
  have hs := conditionalReciprocal_residual_head_energy_le L hL N H
  change _ ≤ sourceBudget at hs
  nlinarith

theorem frequently_energy_iff_signedRemainder
    (H L : ℕ → ℕ) (hL : ∀ N, 0 < L N) :
    (∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      weightedHeadEnergy 2 (H N) (movingCorrection N) ≤ C) ↔
    (∃ A : ℝ, ∃ᶠ N : ℕ in atTop,
      -A ≤ signedRemainder N (L N) (H N) (hL N)) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, hC.mono (fun N hn =>
      signedRemainder_lower_of_energy_le N (L N) (H N) (hL N) C hn)⟩
  · rintro ⟨A, hA⟩
    exact ⟨sourceBudget+A, hA.mono (fun N hn =>
      energy_le_of_signedRemainder_lower N (L N) (H N) (hL N) A hn)⟩

theorem frequently_energy_iff_cross
    (H L : ℕ → ℕ) (hL : ∀ N, 0 < L N) :
    (∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      weightedHeadEnergy 2 (H N) (movingCorrection N) ≤ C) ↔
    (∃ A : ℝ, ∃ᶠ N : ℕ in atTop,
      -A ≤ weightedHeadCross 2 (H N)
        (movingCorrection N) (conditionedRemainder N (L N) (hL N))) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨sourceBudget+2*C, hC.mono (fun N hn =>
      cross_lower_of_energy_le N (L N) (H N) (hL N) C hn)⟩
  · rintro ⟨A, hA⟩
    exact ⟨sourceBudget+2*A, hA.mono (fun N hn =>
      energy_le_of_cross_lower N (L N) (H N) (hL N) A hn)⟩

theorem riemannHypothesis_of_frequently_signedRemainder_lower
    (H L : ℕ → ℕ) (hH : Tendsto H atTop atTop) (hL : ∀ N, 0 < L N)
    (A : ℝ) (hA : ∃ᶠ N : ℕ in atTop,
      -A ≤ signedRemainder N (L N) (H N) (hL N)) : RiemannHypothesis := by
  apply QSquarefreeMovingHeadEnergy.riemannHypothesis_of_frequently_moving_head_energy_bound
    2 H hH (sourceBudget+A)
  exact hA.mono (fun N hn =>
    energy_le_of_signedRemainder_lower N (L N) (H N) (hL N) A hn)

theorem riemannHypothesis_of_frequently_cross_lower
    (H L : ℕ → ℕ) (hH : Tendsto H atTop atTop) (hL : ∀ N, 0 < L N)
    (A : ℝ) (hA : ∃ᶠ N : ℕ in atTop,
      -A ≤ weightedHeadCross 2 (H N)
        (movingCorrection N) (conditionedRemainder N (L N) (hL N))) :
    RiemannHypothesis := by
  apply QSquarefreeMovingHeadEnergy.riemannHypothesis_of_frequently_moving_head_energy_bound
    2 H hH (sourceBudget+2*A)
  exact hA.mono (fun N hn =>
    energy_le_of_cross_lower N (L N) (H N) (hL N) A hn)

theorem riemannHypothesis_of_frequently_absorption
    (H L : ℕ → ℕ) (hH : Tendsto H atTop atTop) (hL : ∀ N, 0 < L N)
    (θ A : ℝ) (hθ : θ < 1)
    (habs : ∃ᶠ N : ℕ in atTop,
      -2 * weightedHeadCross 2 (H N) (movingCorrection N)
        (conditionedRemainder N (L N) (hL N)) ≤
        θ * weightedHeadEnergy 2 (H N) (movingCorrection N) +
          weightedHeadEnergy 2 (H N) (conditionedRemainder N (L N) (hL N)) + A) :
    RiemannHypothesis := by
  apply QSquarefreeMovingHeadEnergy.riemannHypothesis_of_frequently_moving_head_energy_bound
    2 H hH ((sourceBudget+A)/(1-θ))
  exact habs.mono (fun N hn =>
    energy_le_of_absorption N (L N) (H N) (hL N) θ A hθ hn)

theorem cross_tendsto_atBot_of_residual_ne_zero
    (H L : ℕ → ℕ) (hH : Tendsto H atTop atTop) (hL : ∀ N, 0 < L N)
    (hr : ZetaTwoOptimizerStage.limitingResidual ≠ 0) :
    Tendsto (fun N => weightedHeadCross 2 (H N)
      (movingCorrection N) (conditionedRemainder N (L N) (hL N))) atTop atBot := by
  apply tendsto_atBot.2
  intro A
  have hg := QSquarefreeMovingHeadEnergy.moving_head_energy_tendsto_atTop_of_residual_ne_zero
    2 H hH hr
  filter_upwards [hg.eventually (eventually_ge_atTop (sourceBudget-2*A))] with N hN
  have he := conditioned_source_weighted_energy_exact 2 N (L N) (H N) (hL N)
  have hs := conditionalReciprocal_residual_head_energy_le (L N) (hL N) N (H N)
  change _ ≤ sourceBudget at hs
  have ht := energy_nonneg 2 (H N) (conditionedRemainder N (L N) (hL N))
  linarith

theorem signedRemainder_tendsto_atBot_of_residual_ne_zero
    (H L : ℕ → ℕ) (hH : Tendsto H atTop atTop) (hL : ∀ N, 0 < L N)
    (hr : ZetaTwoOptimizerStage.limitingResidual ≠ 0) :
    Tendsto (fun N => signedRemainder N (L N) (H N) (hL N)) atTop atBot := by
  apply tendsto_atBot.2
  intro A
  have hg := QSquarefreeMovingHeadEnergy.moving_head_energy_tendsto_atTop_of_residual_ne_zero
    2 H hH hr
  filter_upwards [hg.eventually (eventually_ge_atTop (sourceBudget-A))] with N hN
  rw [signedRemainder_exact]
  have hs := conditionalReciprocal_residual_head_energy_le (L N) (hL N) N (H N)
  change _ ≤ sourceBudget at hs
  linarith
end RiemannResearch.RH.QSquarefreeCRTCrossCriterion
