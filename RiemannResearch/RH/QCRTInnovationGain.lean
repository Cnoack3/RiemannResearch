/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.OrthogonalObservationInnovation
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.RH.QCRTMovingPredictionGain
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QCRTMinimumHeadCost
import RiemannResearch.RH.QSquarefreeHeadStep
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QSquarefreeGapHeadCost
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QCRTCoprimeApproximation
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual prediction shifts use only newly available observation capacity

Source: continuation of the user-provided moving-prediction cancellation
agenda, 29 October 2026. The enlargement displacement is orthogonal to the
old zero-head tangent. Projecting the new observation normal off that tangent
improves the full-capacity gain bound to a capacity-increment bound.
All norms include the complete Q tail. Zero increments force zero prediction
shift; the exact completion remains valid with totalized real division.
No cumulative arithmetic growth bound is proved here.
-/

namespace RiemannResearch.RH.QCRTInnovationGain
noncomputable section
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace QSquarefreeAffineHead
open QCRTPeriodHeadBalance QSquarefreeHeadStep QCRTMovingPredictionGain
open QSquarefreeEnergyTransitions QSquarefreeGapHeadCost QCRTCoprimeApproximation
open RiemannResearch.Analysis.OrthogonalObservationInnovation
open RiemannResearch.Analysis.FiniteGramCapacity

def oldTangent (i : ℕ) : Submodule ℝ QHilbert :=
  dictionary (conductors (primorial (denseSchedule i + 2))) ⊓ headNull (i + 1)

instance oldTangent_finiteDimensional (i : ℕ) : FiniteDimensional ℝ (oldTangent i) := by
  unfold oldTangent
  infer_instance

def denseNormal (i : ℕ) : QHilbert :=
  stepNormal (i + 2) (primorial (denseSchedule (i + 1) + 2))
    (squarefreeAnchor i) (denseAnchor_mem i)

def denseDisplacement (i : ℕ) : QHilbert :=
  minimumAt (denseSchedule i) (i + 1) -
    minimumAt (denseSchedule (i + 1)) (i + 1)

def innovationNormal (i : ℕ) : QHilbert :=
  innovation (oldTangent i) (denseNormal i)

def innovationCapacity (i : ℕ) : ℝ := ‖innovationNormal i‖ ^ 2

def oldCapacity (i : ℕ) : ℝ :=
  ‖(oldTangent i).starProjection (denseNormal i)‖ ^ 2

def innovationRemainder (i : ℕ) : QHilbert :=
  denseDisplacement i -
    ((nextMismatch i - oldMismatch i) / innovationCapacity i) • innovationNormal i

theorem denseNormal_energy (i : ℕ) : ‖denseNormal i‖ ^ 2 = denseCapacity i :=
  (capacity_eq_norm_sq _ _).symm

theorem capacity_decomposition (i : ℕ) :
    denseCapacity i = oldCapacity i + innovationCapacity i := by
  have h := innovation_energy (oldTangent i) (denseNormal i)
  change innovationCapacity i = ‖denseNormal i‖ ^ 2 - oldCapacity i at h
  rw [denseNormal_energy] at h
  linarith

theorem innovationCapacity_nonneg (i : ℕ) : 0 ≤ innovationCapacity i := sq_nonneg _
theorem oldCapacity_nonneg (i : ℕ) : 0 ≤ oldCapacity i := sq_nonneg _

theorem innovationCapacity_le (i : ℕ) : innovationCapacity i ≤ denseCapacity i := by
  rw [capacity_decomposition]
  exact le_add_of_nonneg_left (oldCapacity_nonneg i)

theorem denseDisplacement_orthogonal_old (i : ℕ) (u : QHilbert)
    (hu : u ∈ oldTangent i) : inner ℝ (denseDisplacement i) u = 0 := by
  have hnew : u ∈ dictionary
      (conductors (primorial (denseSchedule (i + 1) + 2))) ⊓ headNull (i + 1) := by
    refine ⟨?_, hu.2⟩
    rw [← divisorStage_eq_dictionary _ (primorial_pos _)]
    apply divisorStage_mono
      (primorial_dvd_primorial
        (Nat.add_le_add_right (denseSchedule_monotone (Nat.le_succ i)) 2))
    rw [divisorStage_eq_dictionary _ (primorial_pos _)]
    exact hu.1
  have ho := Submodule.starProjection_inner_eq_zero
    (approximant (denseSchedule i)) u hu
  have hn := Submodule.starProjection_inner_eq_zero
    (approximant (denseSchedule (i + 1))) u hnew
  change inner ℝ (minimumAt (denseSchedule i) (i + 1)) u = 0 at ho
  change inner ℝ (minimumAt (denseSchedule (i + 1)) (i + 1)) u = 0 at hn
  rw [denseDisplacement, inner_sub_left, ho, hn, sub_self]

theorem denseDisplacement_mem (i : ℕ) :
    denseDisplacement i ∈ zeroHeadSpan
      (conductors (primorial (denseSchedule (i + 1) + 2)))
      (i + 2 - 1) (squarefreeAnchor i) := by
  rw [← inf_headNull_eq_zeroHeadSpan _ (conductor_gt_one _) (i + 2 - 1)
    (squarefreeAnchor i) (by omega) (denseAnchor_mem i)
    (by have := (squarefreeAnchor_spec i).1; omega)]
  refine ⟨?_, ?_⟩
  · apply Submodule.sub_mem
    · rw [← divisorStage_eq_dictionary _ (primorial_pos _)]
      exact divisorStage_mono
        (primorial_dvd_primorial
          (Nat.add_le_add_right (denseSchedule_monotone (Nat.le_succ i)) 2))
        (minimumAt_mem _ _)
    · rw [← divisorStage_eq_dictionary _ (primorial_pos _)]
      exact minimumAt_mem _ _
  · intro n hn hni
    change qSequenceLinear (_ - _) n = 0
    rw [map_sub, Pi.sub_apply]
    change qSequence (minimumAt (denseSchedule i) (i + 1)) n -
      qSequence (minimumAt (denseSchedule (i + 1)) (i + 1)) n = 0
    rw [minimumAt_head _ _ (by dsimp [denseSchedule]; omega) n hn (by omega),
      minimumAt_head _ _ (by dsimp [denseSchedule]; omega) n hn (by omega), sub_self]

theorem denseDisplacement_pairing (i : ℕ) :
    inner ℝ (denseDisplacement i) (denseNormal i) =
      nextMismatch i - oldMismatch i := by
  rw [denseNormal, stepNormal_pairing _ _ _ (by omega) _
    (squarefreeAnchor_spec i).1 _ (denseDisplacement_mem i)]
  unfold denseDisplacement
  change qSequenceLinear (_ - _) (i + 2) = _
  rw [map_sub, Pi.sub_apply]
  change qSequence (minimumAt (denseSchedule i) (i + 1)) (i + 2) -
    qSequence (minimumAt (denseSchedule (i + 1)) (i + 1)) (i + 2) = _
  dsimp [nextMismatch, oldMismatch]
  ring

theorem innovation_gain_completion (i : ℕ) :
    periodGain denseSchedule i =
      (nextMismatch i - oldMismatch i) ^ 2 / innovationCapacity i +
        ‖innovationRemainder i‖ ^ 2 := by
  have h := innovation_completion (oldTangent i)
    (denseDisplacement i) (denseNormal i) (denseDisplacement_orthogonal_old i)
  rw [denseDisplacement_pairing] at h
  exact h

theorem prediction_shift_sq_le_innovation_gain (i : ℕ) :
    (nextMismatch i - oldMismatch i) ^ 2 ≤
      innovationCapacity i * periodGain denseSchedule i := by
  have h := innovation_source_sq_le (oldTangent i)
    (denseDisplacement i) (denseNormal i) (denseDisplacement_orthogonal_old i)
  rw [denseDisplacement_pairing] at h
  exact h

theorem prediction_eq_of_zero_innovation (i : ℕ) (hi : innovationCapacity i = 0) :
    nextMismatch i = oldMismatch i := by
  have h := prediction_shift_sq_le_innovation_gain i
  rw [hi, zero_mul] at h
  nlinarith [sq_nonneg (nextMismatch i - oldMismatch i)]

theorem dense_innovation_transition (i : ℕ) (hsf : Squarefree (i + 2)) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i =
      nextMismatch i ^ 2 / denseCapacity i -
      (nextMismatch i - oldMismatch i) ^ 2 / innovationCapacity i -
        ‖innovationRemainder i‖ ^ 2 := by
  have hnL : i + 2 ∣ primorial (denseSchedule (i + 1) + 2) :=
    dvd_trans hsf.dvd_primorial
      (primorial_dvd_primorial (by dsimp [denseSchedule]; omega))
  have hc := QCRTMinimumHeadCost.minimumAt_single_head_cost
    (denseSchedule (i + 1)) (i + 2) (squarefreeAnchor i) (by omega)
    (by dsimp [denseSchedule]; omega) hnL (denseAnchor_mem i)
    (squarefreeAnchor_spec i).1
  have hp := minimumAt_period_gain (denseSchedule i) (denseSchedule (i + 1))
    (i + 1) (denseSchedule_monotone (Nat.le_succ i))
    (by dsimp [denseSchedule]; omega)
  have hg := innovation_gain_completion i
  simp only [show i + 2 - 1 = i + 1 by omega] at hc
  change ‖minimumAt (denseSchedule (i + 1)) (i + 2)‖ ^ 2 =
    ‖minimumAt (denseSchedule (i + 1)) (i + 1)‖ ^ 2 +
      nextMismatch i ^ 2 / denseCapacity i at hc
  change ‖minimumAt (denseSchedule i) (i + 1) -
    minimumAt (denseSchedule (i + 1)) (i + 1)‖ ^ 2 = _ at hg
  have he : ‖minimumAt (denseSchedule (i + 1)) (i + 2)‖ ^ 2 -
      ‖minimumAt (denseSchedule i) (i + 1)‖ ^ 2 =
      nextMismatch i ^ 2 / denseCapacity i -
      (nextMismatch i - oldMismatch i) ^ 2 / innovationCapacity i -
        ‖innovationRemainder i‖ ^ 2 := by linarith
  simpa only [stageEnergy, Nat.add_assoc] using he

theorem denseCapacity_pos (i : ℕ) (hsf : Squarefree (i + 2)) :
    0 < denseCapacity i := by
  apply stepCapacity_pos (i + 2) _ _ (by omega) (primorial_pos _)
    _ (denseAnchor_mem i) (squarefreeAnchor_spec i).1
  exact dvd_trans hsf.dvd_primorial
    (primorial_dvd_primorial (by dsimp [denseSchedule]; omega))

def innovationPenalty (i : ℕ) : ℝ :=
  oldCapacity i / innovationCapacity i * (nextMismatch i - oldMismatch i) ^ 2

theorem innovationPenalty_nonneg (i : ℕ) : 0 ≤ innovationPenalty i :=
  mul_nonneg (div_nonneg (oldCapacity_nonneg i) (innovationCapacity_nonneg i))
    (sq_nonneg _)

theorem dense_refined_signed_transition (i : ℕ) (hsf : Squarefree (i + 2)) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i =
      (oldMismatch i * (2 * nextMismatch i - oldMismatch i) - innovationPenalty i) /
        denseCapacity i - ‖innovationRemainder i‖ ^ 2 := by
  have h := refined_transition_algebra (oldMismatch i) (nextMismatch i)
    (denseCapacity i) (innovationCapacity i) (ne_of_gt (denseCapacity_pos i hsf))
    (prediction_eq_of_zero_innovation i)
  have hdiff : denseCapacity i - innovationCapacity i = oldCapacity i := by
    rw [capacity_decomposition]
    ring
  rw [hdiff] at h
  rw [dense_innovation_transition i hsf, h]
  rfl

end
end RiemannResearch.RH.QCRTInnovationGain
