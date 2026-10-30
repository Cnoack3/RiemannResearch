/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTPrimePairCertificate
import RiemannResearch.RH.QCRTTrialCertificate
import RiemannResearch.RH.QCRTHeadFirstSource
import RiemannResearch.RH.QCRTCoprimeApproximation
import RiemannResearch.RH.QCRTInnovationBlock
import RiemannResearch.RH.QCRTInnovationGain
import RiemannResearch.RH.QCRTPrimeInnovation
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.OrthogonalObservationInnovation
import RiemannResearch.Analysis.OrthogonalObservationHeadFirst
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertGram
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Next-head screening and exact full-family certificate transport

Source: the user-provided full-squarefree dyadic agenda of 30 October 2026,
priority 2. Standard orthogonal elimination is also described in O'Leary
and Rust, Variable Projection for Nonlinear Least Squares Problems (2013),
https://www.nist.gov/publications/variable-projection-nonlinear-least-squares-problems
(the reference supports the projection strategy, not these arithmetic statements).

The actual old next-head tangent is used throughout. Source preservation,
the complete mixed Gram correction, and the removed projection energy are exact.
The adjusted family is identified columnwise and for every full synthesis.
No cumulative source estimate or RH claim is asserted.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTScreenedFloorTrial
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace QSquarefreeAffineHead
open QCRTPeriodHeadBalance QSquarefreeEnergyTransitions QCRTPrimePairCertificate
open QCRTPrimeInnovation QCRTInnovationGain
open QCRTCoprimeApproximation QCRTTrialCertificate QCRTInnovationBlock
open RiemannResearch.Analysis.OrthogonalObservationInnovation

def nextTangent (i : ℕ) : Submodule ℝ QHilbert :=
  dictionary (conductors (oldPeriod i)) ⊓ headNull (i + 2)

instance nextTangent_finiteDimensional (i : ℕ) :
    FiniteDimensional ℝ (nextTangent i) := by
  unfold nextTangent
  infer_instance

def screen (i : ℕ) (x : QHilbert) : QHilbert :=
  innovation (nextTangent i) x

theorem nextTangent_le_old (i : ℕ) : nextTangent i ≤ oldTangent i := by
  intro u hu
  exact ⟨hu.1, fun n hn hni => hu.2 n hn (by omega)⟩

theorem headFirst_orthogonal (i : ℕ) (u : QHilbert)
    (hu : u ∈ nextTangent i) : inner ℝ (headFirstMinimum i) u = 0 := by
  exact Submodule.starProjection_inner_eq_zero
    (approximant (denseSchedule i)) u hu

theorem screen_source (i : ℕ) (x : QHilbert) :
    inner ℝ (headFirstMinimum i) (screen i x) =
      inner ℝ (headFirstMinimum i) x :=
  innovation_inner _ _ _ (headFirst_orthogonal i)

theorem screen_energy (i : ℕ) (x : QHilbert) :
    ‖screen i x‖ ^ 2 = ‖x‖ ^ 2 - ‖(nextTangent i).starProjection x‖ ^ 2 :=
  innovation_energy _ _

theorem screen_energy_le (i : ℕ) (x : QHilbert) :
    ‖screen i x‖ ^ 2 ≤ ‖x‖ ^ 2 := innovation_energy_le _ _

theorem screen_head (i : ℕ) (x : QHilbert) (hx : x ∈ headNull (i + 2)) :
    screen i x ∈ headNull (i + 2) :=
  (headNull (i + 2)).sub_mem hx ((nextTangent i).starProjection_apply_mem x).2

theorem screen_mem (i : ℕ) (x : QHilbert)
    (hx : x ∈ divisorStage (primorial (denseSchedule (i + 1) + 2))) :
    screen i x ∈ divisorStage (primorial (denseSchedule (i + 1) + 2)) := by
  apply Submodule.sub_mem _ hx
  apply divisorStage_mono (primorial_dvd_primorial
    (Nat.add_le_add_right (denseSchedule_monotone (Nat.le_succ i)) 2))
  rw [divisorStage_eq_dictionary _ (primorial_pos _)]
  exact ((nextTangent i).starProjection_apply_mem x).1

theorem screen_gram (i : ℕ) (x y : QHilbert) :
    inner ℝ (screen i x) (screen i y) =
      inner ℝ x y - inner ℝ ((nextTangent i).starProjection x)
        ((nextTangent i).starProjection y) := by
  have hx := Submodule.starProjection_inner_eq_zero x
    ((nextTangent i).starProjection y) ((nextTangent i).starProjection_apply_mem y)
  have hy := Submodule.starProjection_inner_eq_zero y
    ((nextTangent i).starProjection x) ((nextTangent i).starProjection_apply_mem x)
  simp only [inner_sub_left] at hx hy
  simp only [screen, innovation, inner_sub_left, inner_sub_right]
  have hy' : inner ℝ ((nextTangent i).starProjection x) y -
      inner ℝ ((nextTangent i).starProjection x) ((nextTangent i).starProjection y) = 0 := by
    simpa only [real_inner_comm] using hy
  linarith

def screenedTrial (i : ℕ) (x : QHilbert) (t : ℝ) : QHilbert :=
  headFirstMinimum i - t • screen i x

theorem screenedTrial_completion (i : ℕ) (hi : 0 < i) (x : QHilbert)
    (hx : x ∈ divisorStage (primorial (denseSchedule (i + 1) + 2)))
    (hh : x ∈ headNull (i + 2)) (t : ℝ) :
    headFirstCost i - 2 * t * inner ℝ (headFirstMinimum i) x +
      t ^ 2 * (‖x‖ ^ 2 - ‖(nextTangent i).starProjection x‖ ^ 2) -
      (stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i) =
      ‖screenedTrial i x t - minimumAt (denseSchedule (i + 1)) (i + 2)‖ ^ 2 := by
  have hm : screenedTrial i x t ∈
      divisorStage (primorial (denseSchedule (i + 1) + 2)) :=
    (divisorStage _).sub_mem
      (divisorStage_mono (primorial_dvd_primorial
        (Nat.add_le_add_right (denseSchedule_monotone (Nat.le_succ i)) 2))
          (minimumAt_mem _ _))
      ((divisorStage _).smul_mem t (screen_mem i x hx))
  have hhead : ∀ n, 0 < n → n ≤ i + 2 → qSequence (screenedTrial i x t) n = 1 := by
    intro n hn hni
    change qSequenceLinear (_ - _) n = _
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change qSequence (headFirstMinimum i) n - t * qSequence (screen i x) n = 1
    rw [screen_head i x hh n hn hni, mul_zero, sub_zero]
    exact minimumAt_head _ _ (by dsimp [denseSchedule]; omega) n hn hni
  have hc := minimumAt_completion (denseSchedule (i + 1)) (i + 2)
    (by dsimp [denseSchedule]; omega) (screenedTrial i x t) hm hhead
  have he : ‖screenedTrial i x t‖ ^ 2 = ‖headFirstMinimum i‖ ^ 2 -
      2 * t * inner ℝ (headFirstMinimum i) x +
      t ^ 2 * (‖x‖ ^ 2 - ‖(nextTangent i).starProjection x‖ ^ 2) := by
    simp only [screenedTrial, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, inner_smul_right, screen_source, screen_energy]
    ring
  have hn : ‖minimumAt (denseSchedule (i + 1)) (i + 2)‖ ^ 2 =
      stageEnergy denseSchedule (i + 1) := by simp only [stageEnergy, Nat.add_assoc]
  rw [he, hn] at hc
  unfold headFirstCost
  linarith


open QCRTHeadFirstSource
open RiemannResearch.Analysis.OrthogonalObservationHeadFirst

theorem mem_nextTangent_iff (i : ℕ) (x : QHilbert) :
    x ∈ nextTangent i ↔ x ∈ oldTangent i ∧ qSequence x (i + 2) = 0 := by
  constructor
  · intro hx
    exact ⟨nextTangent_le_old i hx, hx.2 _ (by omega) le_rfl⟩
  · rintro ⟨hx, hval⟩
    refine ⟨hx.1, ?_⟩
    intro n hn hni
    by_cases he : n = i + 2
    · simpa only [he] using hval
    · exact hx.2 n hn (by omega)

theorem oldNormal_mem (i : ℕ) : oldNormal i ∈ oldTangent i :=
  (oldTangent i).starProjection_apply_mem _

theorem oldNormal_next (i : ℕ) : qSequence (oldNormal i) (i + 2) = oldCapacity i := by
  have h := old_normal_pairing i (oldNormal i) (oldNormal_mem i)
  simpa only [oldNormal, oldCapacity, real_inner_self_eq_norm_sq] using h.symm

theorem oldNormal_orthogonal_next (i : ℕ) (u : QHilbert) (hu : u ∈ nextTangent i) :
    inner ℝ (oldNormal i) u = 0 := by
  rw [real_inner_comm]
  exact (old_normal_pairing i u (nextTangent_le_old i hu)).trans
    (hu.2 _ (by omega) le_rfl)

theorem screen_eq_of_sub_mem (i : ℕ) (x y : QHilbert)
    (hxy : x - y ∈ nextTangent i)
    (hy : ∀ u ∈ nextTangent i, inner ℝ y u = 0) :
    screen i x = y := by
  have hp : (nextTangent i).starProjection x = x - y := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hxy
    intro u hu
    simpa only [sub_sub_cancel] using hy u hu
  simp only [screen, innovation, hp, sub_sub_cancel]

/-- Next-head screening is exactly the adjusted old-head column. -/
theorem screen_eq_adjusted (i : ℕ) (x : QHilbert)
    (hx : x ∈ headNull (i + 2)) (hK : oldCapacity i ≠ 0) :
    screen i x = adjustedColumn (innovation (oldTangent i) x) (oldNormal i)
      (qSequence (innovation (oldTangent i) x) (i + 2)) (oldCapacity i) := by
  let v := innovation (oldTangent i) x
  let c := qSequence v (i + 2)
  let y := v - (c / oldCapacity i) • oldNormal i
  have hvhead : v ∈ headNull (i + 1) :=
    (headNull (i + 1)).sub_mem
      (fun n hn hni => hx n hn (by omega))
      ((oldTangent i).starProjection_apply_mem x).2
  have hyhead : y ∈ headNull (i + 1) :=
    (headNull (i + 1)).sub_mem hvhead
      ((headNull (i + 1)).smul_mem _ (oldNormal_mem i).2)
  have hyval : qSequence y (i + 2) = 0 := by
    change qSequenceLinear (v - (c / oldCapacity i) • oldNormal i) (i + 2) = 0
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change c - c / oldCapacity i * qSequence (oldNormal i) (i + 2) = 0
    rw [oldNormal_next, div_mul_cancel₀ _ hK, sub_self]
  have hxy : x - y ∈ nextTangent i := by
    apply (mem_nextTangent_iff i _).mpr
    constructor
    · have he : x - y = (oldTangent i).starProjection x +
          (c / oldCapacity i) • oldNormal i := by
        dsimp [y, v, innovation]
        abel
      rw [he]
      exact (oldTangent i).add_mem ((oldTangent i).starProjection_apply_mem x)
        ((oldTangent i).smul_mem _ (oldNormal_mem i))
    · change qSequenceLinear (x - y) (i + 2) = 0
      simp only [map_sub, Pi.sub_apply]
      change qSequence x (i + 2) - qSequence y (i + 2) = 0
      rw [hx _ (by omega) le_rfl, hyval, sub_self]
  apply screen_eq_of_sub_mem i x y hxy
  intro u hu
  have ho := Submodule.starProjection_inner_eq_zero x u (nextTangent_le_old i hu)
  change inner ℝ v u = 0 at ho
  simp only [y, inner_sub_left, real_inner_smul_left, ho,
    oldNormal_orthogonal_next i u hu, mul_zero, sub_self]

theorem added_gt_next (i d : ℕ) (hd : d ∈ addedConductors i) : i + 2 < d := by
  have hh := Finset.mem_sdiff.mp hd
  have hn := Finset.mem_filter.mp hh.1
  have hdiv := (Nat.mem_divisors.mp hn.1).1
  have hsf := (squarefree_primorial (denseSchedule (i + 1) + 2)).squarefree_of_dvd hdiv
  by_contra h
  have hold := dvd_trans hsf.dvd_primorial
    (primorial_dvd_primorial (show d ≤ denseSchedule i + 2 by dsimp [denseSchedule]; omega))
  exact hh.2 (Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hold, primorial_ne_zero _⟩, hn.2⟩)

theorem jointFamily_eq_screen (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (d : addedConductors i) :
    jointFamily i d = screen i (compensatedResidue d (oldPeriod i)) := by
  symm
  apply screen_eq_adjusted i _ _ (ne_of_gt (oldCapacity_pos i hi hsf))
  intro n hn hni
  exact compensatedResidue_head d (oldPeriod i) n (by have := added_gt_next i d d.property; omega)
    (by have := next_lt_oldPeriod i hi; omega)
    (by have := added_gt_next i d d.property; omega)
    (by have := next_lt_oldPeriod i hi; omega)


open QCRTMovingPredictionGain
open RiemannResearch.Analysis.FiniteHilbertGram

theorem oldMinimum_orthogonal (i : ℕ) (u : QHilbert) (hu : u ∈ oldTangent i) :
    inner ℝ (minimumAt (denseSchedule i) (i + 1)) u = 0 :=
  Submodule.starProjection_inner_eq_zero (approximant (denseSchedule i)) u hu

/-- The concrete old-dictionary head repair, with its actual old normal. -/
theorem headFirst_eq_repair (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2)) :
    headFirstMinimum i = minimumAt (denseSchedule i) (i + 1) +
      (oldMismatch i / oldCapacity i) • oldNormal i := by
  let f := minimumAt (denseSchedule i) (i + 1)
  let g := f + (oldMismatch i / oldCapacity i) • oldNormal i
  have hK := ne_of_gt (oldCapacity_pos i hi hsf)
  have hmem : headFirstMinimum i - g ∈ nextTangent i := by
    refine ⟨?_, ?_⟩
    · apply Submodule.sub_mem
      · rw [← divisorStage_eq_dictionary _ (show 0 < oldPeriod i from primorial_pos _)]
        exact minimumAt_mem _ _
      · exact (dictionary _).add_mem
          (by
            rw [← divisorStage_eq_dictionary _ (show 0 < oldPeriod i from primorial_pos _)]
            exact minimumAt_mem _ _)
          ((dictionary _).smul_mem _ (oldNormal_mem i).1)
    · intro n hn hni
      change qSequenceLinear (headFirstMinimum i - (f +
        (oldMismatch i / oldCapacity i) • oldNormal i)) n = 0
      simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      change qSequence (headFirstMinimum i) n -
        (qSequence f n + (oldMismatch i / oldCapacity i) * qSequence (oldNormal i) n) = 0
      rw [show qSequence (headFirstMinimum i) n = 1 from
        minimumAt_head _ _ (by dsimp [denseSchedule]; omega) n hn hni]
      by_cases he : n = i + 2
      · subst n
        rw [oldNormal_next, div_mul_cancel₀ _ hK]
        dsimp [oldMismatch, f]
        ring
      · rw [(oldNormal_mem i).2 n hn (by omega),
          show qSequence f n = 1 from minimumAt_head _ _
            (by dsimp [denseSchedule]; omega) n hn (by omega)]
        ring
  have hF := headFirst_orthogonal i _ hmem
  have hf := oldMinimum_orthogonal i _ (nextTangent_le_old i hmem)
  have hk := oldNormal_orthogonal_next i _ hmem
  have hzero : inner ℝ (headFirstMinimum i - g) (headFirstMinimum i - g) = 0 := by
    rw [inner_sub_left, hF]
    simp only [g, inner_add_left, real_inner_smul_left]
    change 0 - (inner ℝ (minimumAt (denseSchedule i) (i + 1))
      (headFirstMinimum i - g) + (oldMismatch i / oldCapacity i) *
        inner ℝ (oldNormal i) (headFirstMinimum i - g)) = 0
    rw [hf, hk]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

theorem headFirstCost_eq (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2)) :
    headFirstCost i = oldMismatch i ^ 2 / oldCapacity i := by
  have hK := ne_of_gt (oldCapacity_pos i hi hsf)
  rw [headFirstCost, headFirst_eq_repair i hi hsf, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right,
    oldMinimum_orthogonal i _ (oldNormal_mem i), mul_zero, add_zero]
  change stageEnergy denseSchedule i +
    (oldMismatch i / oldCapacity i) ^ 2 * oldCapacity i -
      stageEnergy denseSchedule i = _
  field_simp
  ring

theorem jointSource_eq_inner (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (d : addedConductors i) :
    jointSource i d = inner ℝ (jointFamily i d) (headFirstMinimum i) := by
  have hK := ne_of_gt (oldCapacity_pos i hi hsf)
  have hkf : inner ℝ (oldNormal i) (minimumAt (denseSchedule i) (i + 1)) = 0 := by
    simpa only [real_inner_comm] using oldMinimum_orthogonal i _ (oldNormal_mem i)
  rw [headFirst_eq_repair i hi hsf]
  simp only [jointFamily, adjustedColumn, inner_sub_left, inner_add_right,
    real_inner_smul_left, inner_smul_right, block_oldNormal_orthogonal, hkf,
    real_inner_self_eq_norm_sq]
  change inner ℝ (blockFamily i d) (minimumAt (denseSchedule i) (i + 1)) -
    oldMismatch i * observation i d / oldCapacity i =
    inner ℝ (blockFamily i d) (minimumAt (denseSchedule i) (i + 1)) -
    observation i d / oldCapacity i * 0 +
    oldMismatch i / oldCapacity i *
      (0 - observation i d / oldCapacity i * oldCapacity i)
  field_simp
  ring

/-- The adjusted certificate is the physical head-first trial energy. -/
theorem trialCertificate_physical (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (t : addedConductors i → ℝ) :
    trialCertificate i t = headFirstCost i -
      2 * inner ℝ (headFirstMinimum i) (Fintype.linearCombination ℝ (jointFamily i) t) +
      ‖Fintype.linearCombination ℝ (jointFamily i) t‖ ^ 2 := by
  classical
  rw [trialCertificate, headFirstCost_eq i hi hsf, gramMatrix_quadratic,
    jointFamily_gram i (ne_of_gt (oldCapacity_pos i hi hsf))]
  congr 2
  rw [real_inner_comm, inner_synthesis_left]
  simp only [dotProduct, jointSource_eq_inner i hi hsf]

/-- Exact transport of any full raw conductor combination into the adjusted family. -/
theorem jointSynthesis_eq_screen (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (t : addedConductors i → ℝ) :
    Fintype.linearCombination ℝ (jointFamily i) t =
      screen i (∑ d : addedConductors i, t d • compensatedResidue d (oldPeriod i)) := by
  classical
  simp only [Fintype.linearCombination_apply, jointFamily_eq_screen i hi hsf]
  change (∑ d, t d • innovationMap (nextTangent i)
    (compensatedResidue d (oldPeriod i))) =
      innovationMap (nextTangent i) (∑ d, t d • compensatedResidue d (oldPeriod i))
  simp only [map_sum, map_smul]

/-- Exact certificate improvement over the corresponding raw full-family trial. -/
theorem trialCertificate_screen_transport (i : ℕ) (hi : 0 < i)
    (hsf : Squarefree (i + 2)) (t : addedConductors i → ℝ) :
    let x := ∑ d : addedConductors i, t d • compensatedResidue d (oldPeriod i)
    trialCertificate i t = headFirstCost i -
      2 * inner ℝ (headFirstMinimum i) x + ‖x‖ ^ 2 -
        ‖(nextTangent i).starProjection x‖ ^ 2 := by
  dsimp only
  rw [trialCertificate_physical i hi hsf, jointSynthesis_eq_screen i hi hsf,
    screen_source, screen_energy]
  ring
end RiemannResearch.RH.QCRTScreenedFloorTrial
