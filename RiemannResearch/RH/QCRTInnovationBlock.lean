/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.OrthogonalObservationInnovation
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.RH.QResidueHeadExtension
import RiemannResearch.RH.QCRTPrimeInnovation
import RiemannResearch.RH.QCRTInnovationGain
import RiemannResearch.RH.QCRTMovingPredictionGain
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QSquarefreeHeadStep
import RiemannResearch.RH.QSquarefreeGapHeadCost
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QCRTCoprimeApproximation
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# The actual innovation block and its three complete inverse-Gram sources

Source: the user-provided capacity-increment agenda, 29 October 2026,
Priority A. The basis is indexed by the exact set of newly admitted conductors,
including an empty set when no conductor is added. Its independence, span,
observation source, displacement source, and all three Gram formulae are
proved for the actual dense minimum-energy family. No asymptotic estimate
or Riemann Hypothesis is assumed or proved.
-/

noncomputable section
namespace RiemannResearch.RH.QCRTInnovationBlock
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace QSquarefreeAffineHead
open QCRTInnovationGain QSquarefreeEnergyTransitions QCRTPrimeInnovation
open QCRTPeriodHeadBalance QSquarefreeHeadStep QSquarefreeGapHeadCost QCRTMovingPredictionGain
open RiemannResearch.Analysis.OrthogonalObservationInnovation
open RiemannResearch.Analysis.FiniteHilbertGram
open QResidueHeadExtension

def newTangent (i : ℕ) : Submodule ℝ QHilbert :=
  dictionary (conductors (primorial (denseSchedule (i + 1) + 2))) ⊓ headNull (i + 1)

instance newTangent_finiteDimensional (i : ℕ) : FiniteDimensional ℝ (newTangent i) := by
  unfold newTangent
  infer_instance

def innovationSpace (i : ℕ) : Submodule ℝ QHilbert :=
  newTangent i ⊓ (oldTangent i)ᗮ

instance innovationSpace_finiteDimensional (i : ℕ) :
    FiniteDimensional ℝ (innovationSpace i) := by
  unfold innovationSpace
  infer_instance

def addedConductors (i : ℕ) : Finset ℕ :=
  conductors (primorial (denseSchedule (i + 1) + 2)) \ conductors (oldPeriod i)

def blockFamily (i : ℕ) : ↥(addedConductors i) → QHilbert :=
  fun d => innovation (oldTangent i) (compensatedResidue d (oldPeriod i))

theorem conductor_inclusion (i : ℕ) :
    conductors (oldPeriod i) ⊆ conductors (primorial (denseSchedule (i + 1) + 2)) := by
  intro d hd
  have hf := Finset.mem_filter.mp hd
  have hdiv := (Nat.mem_divisors.mp hf.1).1
  have hn := dvd_trans hdiv (primorial_dvd_primorial
    (show denseSchedule i + 2 ≤ denseSchedule (i + 1) + 2 by dsimp [denseSchedule]; omega))
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hn, primorial_ne_zero _⟩, hf.2⟩

theorem added_gt_head (i d : ℕ) (hd : d ∈ addedConductors i) : i + 1 < d := by
  have hh := Finset.mem_sdiff.mp hd
  have hnew := Finset.mem_filter.mp hh.1
  have hdiv := (Nat.mem_divisors.mp hnew.1).1
  have hsf := (squarefree_primorial (denseSchedule (i + 1) + 2)).squarefree_of_dvd hdiv
  by_contra h
  have hdsmall : d ≤ denseSchedule i + 2 := by dsimp [denseSchedule]; omega
  have hold := dvd_trans hsf.dvd_primorial (primorial_dvd_primorial hdsmall)
  exact hh.2 (Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hold, primorial_ne_zero _⟩, hnew.2⟩)

theorem block_independent (i : ℕ) : LinearIndependent ℝ (blockFamily i) := by
  exact screened_added_independent _ _ (i + 1) (oldPeriod i)
    (conductor_gt_one _) (conductor_gt_one _) (conductor_inclusion i) (by omega)
    (oldPeriod_mem i) (head_lt_oldPeriod i) (added_gt_head i)

theorem block_span (i : ℕ) :
    synthesisSpan (blockFamily i) = innovationSpace i := by
  exact screened_added_span _ _ (i + 1) (oldPeriod i)
    (conductor_gt_one _) (conductor_gt_one _) (conductor_inclusion i) (by omega)
    (oldPeriod_mem i) (head_lt_oldPeriod i) (added_gt_head i)

theorem oldTangent_le_new (i : ℕ) : oldTangent i ≤ newTangent i := by
  intro x hx
  refine ⟨?_, hx.2⟩
  apply (Submodule.span_mono ?_) hx.1
  rintro y ⟨d, rfl⟩
  exact ⟨⟨d, conductor_inclusion i d.property⟩, rfl⟩

theorem newTangent_eq_zeroHeadSpan (i : ℕ) :
    newTangent i = zeroHeadSpan
      (conductors (primorial (denseSchedule (i + 1) + 2))) (i + 2 - 1)
      (squarefreeAnchor i) := by
  unfold newTangent
  rw [show i + 1 = i + 2 - 1 by omega]
  exact inf_headNull_eq_zeroHeadSpan _ (conductor_gt_one _) _ _
    (by omega) (denseAnchor_mem i) (by have := (squarefreeAnchor_spec i).1; omega)

theorem denseNormal_mem_new (i : ℕ) : denseNormal i ∈ newTangent i := by
  rw [newTangent_eq_zeroHeadSpan]
  exact stepNormal_mem _ _ _ _

theorem innovationNormal_mem (i : ℕ) : innovationNormal i ∈ innovationSpace i := by
  refine ⟨?_, Submodule.sub_starProjection_mem_orthogonal _⟩
  exact (newTangent i).sub_mem (denseNormal_mem_new i)
    (oldTangent_le_new i ((oldTangent i).starProjection_apply_mem _))

theorem displacement_mem (i : ℕ) : denseDisplacement i ∈ innovationSpace i := by
  constructor
  · rw [newTangent_eq_zeroHeadSpan]
    exact denseDisplacement_mem i
  · apply (Submodule.mem_orthogonal _ _).mpr
    intro u hu
    rw [real_inner_comm]
    exact denseDisplacement_orthogonal_old i u hu

theorem project_normal (i : ℕ) :
    (innovationSpace i).starProjection (denseNormal i) = innovationNormal i := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (innovationNormal_mem i)
  intro w hw
  have ho := ((oldTangent i).mem_orthogonal w).mp hw.2
    ((oldTangent i).starProjection (denseNormal i))
    ((oldTangent i).starProjection_apply_mem _)
  have he : denseNormal i - innovationNormal i =
      (oldTangent i).starProjection (denseNormal i) := by
    unfold innovationNormal innovation
    abel
  rw [he]
  exact ho

theorem project_optimizer (i : ℕ) :
    (innovationSpace i).starProjection (minimumAt (denseSchedule i) (i + 1)) =
      denseDisplacement i := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (displacement_mem i)
  intro w hw
  have he : minimumAt (denseSchedule i) (i + 1) - denseDisplacement i =
      minimumAt (denseSchedule (i + 1)) (i + 1) := by
    unfold denseDisplacement
    abel
  rw [he]
  exact Submodule.starProjection_inner_eq_zero
    (QCRTCoprimeApproximation.approximant (denseSchedule (i + 1))) w hw.1

theorem block_observation (i : ℕ) (d : addedConductors i) :
    cross (blockFamily i) (denseNormal i) d = qSequence (blockFamily i d) (i + 2) := by
  have hm : blockFamily i d ∈ innovationSpace i := by
    rw [← block_span]
    exact Submodule.subset_span ⟨d, rfl⟩
  have hn := hm.1
  rw [newTangent_eq_zeroHeadSpan] at hn
  exact stepNormal_pairing _ _ _ (by omega) _ (squarefreeAnchor_spec i).1 _ hn

theorem gain_inverseGram (i : ℕ) :
    periodGain denseSchedule i =
      dotProduct (cross (blockFamily i) (minimumAt (denseSchedule i) (i + 1)))
        ((gramMatrix (blockFamily i))⁻¹.mulVec
          (cross (blockFamily i) (minimumAt (denseSchedule i) (i + 1)))) := by
  have h := projection_inner_eq_inverseGram (block_independent i)
    (minimumAt (denseSchedule i) (i + 1)) (minimumAt (denseSchedule i) (i + 1))
  simp only [block_span, project_optimizer, real_inner_self_eq_norm_sq] at h
  exact h

theorem capacity_inverseGram (i : ℕ) :
    innovationCapacity i =
      dotProduct (cross (blockFamily i) (denseNormal i))
        ((gramMatrix (blockFamily i))⁻¹.mulVec (cross (blockFamily i) (denseNormal i))) := by
  have h := projection_inner_eq_inverseGram (block_independent i) (denseNormal i) (denseNormal i)
  simp only [block_span, project_normal, real_inner_self_eq_norm_sq] at h
  exact h

theorem prediction_inverseGram (i : ℕ) :
    nextMismatch i - oldMismatch i =
      dotProduct (cross (blockFamily i) (denseNormal i))
        ((gramMatrix (blockFamily i))⁻¹.mulVec
          (cross (blockFamily i) (minimumAt (denseSchedule i) (i + 1)))) := by
  have h := projection_inner_eq_inverseGram (block_independent i) (denseNormal i)
    (minimumAt (denseSchedule i) (i + 1))
  simp only [block_span, project_normal, project_optimizer] at h
  rw [real_inner_comm] at h
  change inner ℝ (denseDisplacement i) (innovation (oldTangent i) (denseNormal i)) = _ at h
  rw [innovation_inner _ _ _ (denseDisplacement_orthogonal_old i), denseDisplacement_pairing] at h
  exact h
end RiemannResearch.RH.QCRTInnovationBlock

namespace RiemannResearch.RH.QCRTInnovationBlock
open ZetaTwoHilbert QCRTInnovationGain QCRTMovingPredictionGain QCRTPeriodHeadBalance
open QSquarefreeHeadStep QSquarefreeEnergyTransitions
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.OrthogonalObservationInnovation

/-- Complete signed transition in the actual screened block. The physical
observation source and the optimizer source use the same complete Gram inverse. -/
theorem dense_block_transition (i : ℕ) (hsf : Squarefree (i + 2)) :
    let v := blockFamily i
    let c := fun d => qSequence (v d) (i + 2)
    let f := cross v (minimumAt (denseSchedule i) (i + 1))
    let B := gramMatrix v
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i =
      (oldMismatch i + dotProduct c (B⁻¹.mulVec f)) ^ 2 /
        (oldCapacity i + dotProduct c (B⁻¹.mulVec c)) -
      dotProduct f (B⁻¹.mulVec f) := by
  dsimp only
  have hc : (fun d => qSequence (blockFamily i d) (i + 2)) =
      cross (blockFamily i) (denseNormal i) := by
    funext d
    exact (block_observation i d).symm
  rw [hc, ← prediction_inverseGram, ← capacity_inverseGram, ← gain_inverseGram,
    ← capacity_decomposition]
  have ha : oldMismatch i + (nextMismatch i - oldMismatch i) = nextMismatch i := by ring
  rw [ha]
  have ht := dense_innovation_transition i hsf
  have hg := innovation_gain_completion i
  linarith

/-- The paper old-capacity square completion, now for the actual optimizers.
The two displayed nonzero capacities are explicit hypotheses, not a growth provider. -/
theorem dense_old_capacity_completion (i : ℕ) (hsf : Squarefree (i + 2))
    (hK : oldCapacity i ≠ 0) (hh : innovationCapacity i ≠ 0) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i =
      oldMismatch i ^ 2 / oldCapacity i -
        (oldCapacity i * nextMismatch i - denseCapacity i * oldMismatch i) ^ 2 /
          (oldCapacity i * innovationCapacity i * denseCapacity i) -
        ‖innovationRemainder i‖ ^ 2 := by
  have hk : oldCapacity i + innovationCapacity i ≠ 0 := by
    rw [← capacity_decomposition]
    exact ne_of_gt (denseCapacity_pos i hsf)
  rw [dense_innovation_transition i hsf, capacity_decomposition,
    old_capacity_completion _ _ _ _ hK hh hk]
end RiemannResearch.RH.QCRTInnovationBlock
