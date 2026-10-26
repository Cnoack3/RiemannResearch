/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QReciprocalVariational
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QProjectionMoments
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Tactic.Linarith

/-!
# Uniform intrinsic dual energy of the actual squarefree correction
Source: the user's weighted-energy research agenda, 26 October 2026.
The complete positive-square remainder is retained. These are unconditional
bounds in the reciprocal form. Transferring them to the unbounded logarithmic
head-energy form remains an Open arithmetic obligation.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeIntrinsicEnergy
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeSmoothedProjection

/-- The projection preserves all pairings against a legal stage vector. -/
theorem movingCorrection_pairing (N : ℕ) (v : QHilbert) (hv : v ∈ stage N) :
    inner ℝ (B (residual N)) v = inner ℝ (movingCorrection N) v := by
  have ho := Submodule.starProjection_inner_eq_zero (B (residual N)) v hv
  rw [inner_sub_left] at ho
  change inner ℝ (B (residual N)) v - inner ℝ (movingCorrection N) v = 0 at ho
  exact sub_eq_zero.mp ho

/-- Unconditional identity for the actual moving squarefree correction. -/
theorem movingCorrection_variational_identity
    (N : ℕ) (v : QHilbert) (hv : v ∈ stage N) :
    inner ℝ (residual N) (B (residual N)) -
      (2 * inner ℝ (movingCorrection N) v - inner ℝ v (B v)) =
        inner ℝ (residual N - v) (B (residual N - v)) := by
  rw [← movingCorrection_pairing N v hv]
  exact B_variational_identity (residual N) v

/-- No arithmetic transfer estimate is needed for this intrinsic dual bound. -/
theorem movingCorrection_variational_le_residual_energy
    (N : ℕ) (v : QHilbert) (hv : v ∈ stage N) :
    2 * inner ℝ (movingCorrection N) v - inner ℝ v (B v) ≤
      inner ℝ (residual N) (B (residual N)) := by
  have hid := movingCorrection_variational_identity N v hv
  have hpos := B_positive (residual N - v)
  linarith

theorem residual_B_energy_le_half_error (N : ℕ) :
    inner ℝ (residual N) (B (residual N)) ≤ error N / 2 :=
  B_energy_le_half_norm_sq (residual N)

theorem residual_B_energy_le_half (N : ℕ) :
    inner ℝ (residual N) (B (residual N)) ≤ (1 : ℝ) / 2 := by
  have h := B_energy_le_half_norm_sq (residual N)
  have he : ‖residual N‖ ^ 2 = 1 - ‖optimizer N‖ ^ 2 :=
    qProjection_error_eq (stage N)
  nlinarith [sq_nonneg ‖optimizer N‖]

/-- Uniform intrinsic dual energy, independent of the stage and test vector. -/
theorem movingCorrection_variational_le_half
    (N : ℕ) (v : QHilbert) (hv : v ∈ stage N) :
    2 * inner ℝ (movingCorrection N) v - inner ℝ v (B v) ≤ (1 : ℝ) / 2 :=
  (movingCorrection_variational_le_residual_energy N v hv).trans
    (residual_B_energy_le_half N)

/-- The same unconditional dual estimate in homogeneous squared form. -/
theorem movingCorrection_B_cauchy_sq
    (N : ℕ) (v : QHilbert) (hv : v ∈ stage N) :
    (inner ℝ (movingCorrection N) v) ^ 2 ≤
      inner ℝ (residual N) (B (residual N)) * inner ℝ v (B v) := by
  rw [← movingCorrection_pairing N v hv]
  exact B_cauchy_sq (residual N) v

end RiemannResearch.RH.QSquarefreeIntrinsicEnergy
