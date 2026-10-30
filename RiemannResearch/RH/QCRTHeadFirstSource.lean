/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.OrthogonalObservationHeadFirst
import RiemannResearch.Analysis.FiniteHilbertGramHeadFirst
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.OrthogonalObservationInnovation
import RiemannResearch.RH.QCRTInnovationBlock
import RiemannResearch.RH.QCRTInnovationGain
import RiemannResearch.RH.QCRTMovingPredictionGain
import RiemannResearch.RH.QCRTPrimeInnovation
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Actual joint sources after imposing the head first

Source: user-provided innovation-space research agenda, 29 October 2026.
The exact full-basis identity and complete-Q row inequality apply to the
actual dense optimizers. Old-capacity positivity is proved at every squarefree
site after the initial step. No all-stage arithmetic growth bound is asserted.
-/

noncomputable section
namespace RiemannResearch.RH.QCRTHeadFirstSource
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace QSquarefreeAffineHead
open QCRTInnovationGain QCRTInnovationBlock QCRTPrimeInnovation QCRTMovingPredictionGain
open QSquarefreeEnergyTransitions QSquarefreeHeadStep QSquarefreeGapHeadCost

/-- After the initial stage, even the next observation site lies strictly
below the old primorial anchor. -/
theorem next_lt_oldPeriod (i : ℕ) (hi : 0 < i) : i + 2 < oldPeriod i := by
  have hs := shortAnchor_spec i
  have hd := (Nat.mem_divisors.mp (Finset.mem_filter.mp (shortAnchor_mem i)).1).1
  have hrL : shortAnchor i ≤ oldPeriod i := Nat.le_of_dvd (primorial_pos _) hd
  have hnr : i + 2 ≤ shortAnchor i := by omega
  have htwo : 2 ∣ oldPeriod i := by
    exact dvd_trans Nat.prime_two.squarefree.dvd_primorial
      (primorial_dvd_primorial (show 2 ≤ denseSchedule i + 2 by
        dsimp [denseSchedule]
        omega))
  by_contra hnL
  have he : oldPeriod i = shortAnchor i := by omega
  rw [he] at htwo
  have hp := (Nat.dvd_prime hs.1).mp htwo
  rcases hp with hp | hp <;> omega

theorem old_normal_pairing (i : ℕ) (u : QHilbert) (hu : u ∈ oldTangent i) :
    inner ℝ u ((oldTangent i).starProjection (denseNormal i)) =
      qSequence u (i + 2) := by
  have hn := oldTangent_le_new i hu
  rw [newTangent_eq_zeroHeadSpan] at hn
  have hp := stepNormal_pairing (i + 2)
    (primorial (denseSchedule (i + 1) + 2)) (squarefreeAnchor i)
    (by omega) (denseAnchor_mem i) (squarefreeAnchor_spec i).1 u hn
  change inner ℝ u (denseNormal i) = qSequence u (i + 2) at hp
  have ho := Submodule.starProjection_inner_eq_zero (denseNormal i) u hu
  have ho' : inner ℝ u
      (denseNormal i - (oldTangent i).starProjection (denseNormal i)) = 0 := by
    simpa only [real_inner_comm] using ho
  rw [inner_sub_right] at ho'
  linarith

/-- The old observation capacity is automatically positive at every
post-initial squarefree site. No new capacity hypothesis is needed there. -/
theorem oldCapacity_pos (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2)) :
    0 < oldCapacity i := by
  have hnL : i + 2 ∣ oldPeriod i :=
    dvd_trans hsf.dvd_primorial
      (primorial_dvd_primorial (show i + 2 ≤ denseSchedule i + 2 by
        dsimp [denseSchedule]
        omega))
  have hnmem : i + 2 ∈ conductors (oldPeriod i) :=
    Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hnL, primorial_ne_zero _⟩, by omega⟩
  let t := compensatedResidue (i + 2) (oldPeriod i)
  have ht : t ∈ oldTangent i := by
    constructor
    · exact (dictionary (conductors (oldPeriod i))).sub_mem
        (Submodule.subset_span ⟨⟨i + 2, hnmem⟩, rfl⟩)
        ((dictionary (conductors (oldPeriod i))).smul_mem _
          (Submodule.subset_span ⟨⟨oldPeriod i, oldPeriod_mem i⟩, rfl⟩))
    · intro m hm hmi
      exact compensatedResidue_head (i + 2) (oldPeriod i) m
        (by omega) (by have := next_lt_oldPeriod i hi; omega)
        (by omega) (by have := next_lt_oldPeriod i hi; omega)
  have hvalue : qSequence t (i + 2) = -1 := by
    simpa [t] using compensatedResidue_next (i + 2) (i + 2)
      (oldPeriod i) (by omega) le_rfl (next_lt_oldPeriod i hi)
  have hp := old_normal_pairing i t ht
  rw [hvalue] at hp
  by_contra hnot
  have hz : oldCapacity i = 0 :=
    le_antisymm (le_of_not_gt hnot) (oldCapacity_nonneg i)
  have hkzero : (oldTangent i).starProjection (denseNormal i) = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  rw [hkzero, inner_zero_right] at hp
  norm_num at hp

end RiemannResearch.RH.QCRTHeadFirstSource

noncomputable section
namespace RiemannResearch.RH.QCRTHeadFirstSource
open ZetaTwoHilbert QCRTInnovationGain QCRTInnovationBlock QCRTMovingPredictionGain
open QCRTPeriodHeadBalance QSquarefreeEnergyTransitions QSquarefreeAffineHead
open QCRTCoprimeApproximation
open RiemannResearch.Analysis.OrthogonalObservationInnovation
open RiemannResearch.Analysis.OrthogonalObservationHeadFirst
open RiemannResearch.Analysis.FiniteHilbertGram

/-- A joint-source estimate for every column of the actual full innovation
block. This uses the complete Q norm and keeps the observation correction. -/
theorem dense_joint_source_sq_le (i : ℕ) (hsf : Squarefree (i + 2))
    (hK : oldCapacity i ≠ 0) (d : addedConductors i) :
    (cross (blockFamily i) (minimumAt (denseSchedule i) (i + 1)) d -
      oldMismatch i * qSequence (blockFamily i d) (i + 2) / oldCapacity i) ^ 2 ≤
    (oldMismatch i ^ 2 / oldCapacity i -
      (stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i)) *
    (‖blockFamily i d‖ ^ 2 +
      qSequence (blockFamily i d) (i + 2) ^ 2 / oldCapacity i) := by
  let k := (oldTangent i).starProjection (denseNormal i)
  let x := blockFamily i d
  have hk_mem : k ∈ oldTangent i := (oldTangent i).starProjection_apply_mem _
  have hx_mem : x ∈ innovationSpace i := by
    change blockFamily i d ∈ innovationSpace i
    rw [← block_span]
    exact Submodule.subset_span ⟨d, rfl⟩
  have hxorth (u : QHilbert) (hu : u ∈ oldTangent i) : inner ℝ x u = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal _ _).mp hx_mem.2 u hu
  have hDk : inner ℝ (denseDisplacement i) k = 0 :=
    denseDisplacement_orthogonal_old i k hk_mem
  have hellk : inner ℝ (innovationNormal i) k = 0 := by
    exact Submodule.starProjection_inner_eq_zero (denseNormal i) k hk_mem
  have hxk : inner ℝ k x = 0 := by simpa only [real_inner_comm] using hxorth k hk_mem
  have hellx : inner ℝ (innovationNormal i) x = qSequence x (i + 2) := by
    rw [real_inner_comm]
    change inner ℝ x (innovation (oldTangent i) (denseNormal i)) = _
    rw [innovation_inner _ _ _ hxorth]
    exact block_observation i d
  have hDell : inner ℝ (denseDisplacement i) (innovationNormal i) =
      nextMismatch i - oldMismatch i := by
    change inner ℝ (denseDisplacement i) (innovation (oldTangent i) (denseNormal i)) = _
    rw [innovation_inner _ _ _ (denseDisplacement_orthogonal_old i)]
    exact denseDisplacement_pairing i
  have hell : ‖innovationNormal i‖ ^ 2 = denseCapacity i - oldCapacity i := by
    have hh := capacity_decomposition i
    change denseCapacity i = oldCapacity i + ‖innovationNormal i‖ ^ 2 at hh
    linarith
  have hDx : inner ℝ (denseDisplacement i) x =
      cross (blockFamily i) (minimumAt (denseSchedule i) (i + 1)) d := by
    have hZ := Submodule.starProjection_inner_eq_zero
      (approximant (denseSchedule (i + 1))) x hx_mem.1
    change inner ℝ (minimumAt (denseSchedule (i + 1)) (i + 1)) x = 0 at hZ
    rw [denseDisplacement, inner_sub_left, hZ, sub_zero, real_inner_comm]
    rfl
  have htransition : stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i =
      nextMismatch i ^ 2 / denseCapacity i - ‖denseDisplacement i‖ ^ 2 := by
    have ht := dense_innovation_transition i hsf
    have hg := innovation_gain_completion i
    change ‖denseDisplacement i‖ ^ 2 = _ at hg
    linarith
  have hh := joint_source_sq_le (denseDisplacement i) k (innovationNormal i) x
    (oldMismatch i) (nextMismatch i) (oldCapacity i) (denseCapacity i)
    (qSequence x (i + 2)) hK (ne_of_gt (denseCapacity_pos i hsf))
    (show ‖k‖ ^ 2 = oldCapacity i from rfl) hell hDk hellk hDell hxk hellx
  rw [hDx, ← htransition] at hh
  exact hh

end RiemannResearch.RH.QCRTHeadFirstSource

noncomputable section
namespace RiemannResearch.RH.QCRTHeadFirstSource
open ZetaTwoHilbert QCRTInnovationGain QCRTInnovationBlock QCRTMovingPredictionGain
open QCRTPeriodHeadBalance QSquarefreeEnergyTransitions QSquarefreeAffineHead
open QCRTCoprimeApproximation
open RiemannResearch.Analysis.OrthogonalObservationInnovation
open RiemannResearch.Analysis.OrthogonalObservationHeadFirst
open RiemannResearch.Analysis.FiniteHilbertGram

/-- The actual head-first inverse-Gram transition at every post-initial
squarefree site. Old capacity positivity is proved, not assumed. -/
theorem dense_headFirst_inverseGram (i : ℕ) (hi : 0 < i)
    (hsf : Squarefree (i + 2)) :
    let v := blockFamily i
    let c := fun d => qSequence (v d) (i + 2)
    let f := cross v (minimumAt (denseSchedule i) (i + 1))
    let r := fun d => f d - oldMismatch i * c d / oldCapacity i
    let B' : Matrix (addedConductors i) (addedConductors i) ℝ :=
      fun d e => gramMatrix v d e + c d * c e / oldCapacity i
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i =
      oldMismatch i ^ 2 / oldCapacity i - dotProduct r (B'⁻¹.mulVec r) := by
  classical
  dsimp only
  let k := (oldTangent i).starProjection (denseNormal i)
  have hK := ne_of_gt (oldCapacity_pos i hi hsf)
  have hk_mem : k ∈ oldTangent i := (oldTangent i).starProjection_apply_mem _
  have hx_mem (d : addedConductors i) : blockFamily i d ∈ innovationSpace i := by
    rw [← block_span]
    exact Submodule.subset_span ⟨d, rfl⟩
  have hxorth (d : addedConductors i) (u : QHilbert) (hu : u ∈ oldTangent i) :
      inner ℝ (blockFamily i d) u = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal _ _).mp (hx_mem d).2 u hu
  have hDk : inner ℝ (denseDisplacement i) k = 0 :=
    denseDisplacement_orthogonal_old i k hk_mem
  have hellk : inner ℝ (innovationNormal i) k = 0 := by
    exact Submodule.starProjection_inner_eq_zero (denseNormal i) k hk_mem
  have hellx (d : addedConductors i) :
      inner ℝ (innovationNormal i) (blockFamily i d) =
        qSequence (blockFamily i d) (i + 2) := by
    rw [real_inner_comm]
    change inner ℝ (blockFamily i d) (innovation (oldTangent i) (denseNormal i)) = _
    rw [innovation_inner _ _ _ (hxorth d)]
    exact block_observation i d
  have hDell : inner ℝ (denseDisplacement i) (innovationNormal i) =
      nextMismatch i - oldMismatch i := by
    change inner ℝ (denseDisplacement i) (innovation (oldTangent i) (denseNormal i)) = _
    rw [innovation_inner _ _ _ (denseDisplacement_orthogonal_old i)]
    exact denseDisplacement_pairing i
  have hell : ‖innovationNormal i‖ ^ 2 = denseCapacity i - oldCapacity i := by
    have hh := capacity_decomposition i
    change denseCapacity i = oldCapacity i + ‖innovationNormal i‖ ^ 2 at hh
    linarith
  have hFk : inner ℝ k (minimumAt (denseSchedule i) (i + 1)) = 0 := by
    have ho := Submodule.starProjection_inner_eq_zero
      (approximant (denseSchedule i)) k hk_mem
    change inner ℝ (minimumAt (denseSchedule i) (i + 1)) k = 0 at ho
    simpa only [real_inner_comm] using ho
  have hD : denseDisplacement i ∈ synthesisSpan (blockFamily i) := by
    rw [block_span]
    exact displacement_mem i
  have he : innovationNormal i ∈ synthesisSpan (blockFamily i) := by
    rw [block_span]
    exact innovationNormal_mem i
  have hDF (d : addedConductors i) :
      inner ℝ (denseDisplacement i) (blockFamily i d) =
        inner ℝ (minimumAt (denseSchedule i) (i + 1)) (blockFamily i d) := by
    have hZ := Submodule.starProjection_inner_eq_zero
      (approximant (denseSchedule (i + 1))) (blockFamily i d) (hx_mem d).1
    change inner ℝ (minimumAt (denseSchedule (i + 1)) (i + 1))
      (blockFamily i d) = 0 at hZ
    rw [denseDisplacement, inner_sub_left, hZ, sub_zero]
  have htransition : stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i =
      nextMismatch i ^ 2 / denseCapacity i - ‖denseDisplacement i‖ ^ 2 := by
    have ht := dense_innovation_transition i hsf
    have hg := innovation_gain_completion i
    change ‖denseDisplacement i‖ ^ 2 = _ at hg
    linarith
  have h := headFirst_inverseGram (blockFamily i) (block_independent i)
    (denseDisplacement i) (minimumAt (denseSchedule i) (i + 1)) k (innovationNormal i)
    (oldMismatch i) (nextMismatch i) (oldCapacity i) (denseCapacity i)
    hK (ne_of_gt (denseCapacity_pos i hsf))
    (show ‖k‖ ^ 2 = oldCapacity i from rfl) hell hDk hellk hDell hFk
    (fun d => hxorth d k hk_mem) hD he hDF
  dsimp only at h
  simp only [hellx] at h
  rw [← htransition] at h
  simpa only [gramMatrix, cross] using h

end RiemannResearch.RH.QCRTHeadFirstSource
