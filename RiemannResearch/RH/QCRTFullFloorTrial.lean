/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTPrimePairCertificate
import RiemannResearch.RH.QFloorDilationEnergy
import RiemannResearch.RH.QCRTPrimeInnovation
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.QCRTDivisorBlock
import RiemannResearch.RH.QFloorDilationHeadEnergy
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete-Q trials from the entire previous divisor dictionary

Source: the user-provided full-squarefree research handoff of 30 October 2026,
priority 2, and the existing complete-Q floor-dilation identities. The actual
unrestricted optimizer is used. Exact competitor and head-tail loss terms
precede inequalities. No pointwise optimizer positivity or source lower bound
is assumed. Wolfram was used only to check the scalar minimization algebra;
all stated results are proved in Lean.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTFullFloorTrial
open ZetaTwoHilbert QSquarefreeLatticePackets QCRTPeriodHeadBalance
open QSquarefreeEnergyTransitions QCRTPrimePairCertificate QCRTPrimeInnovation QFloorDilation

/-- Explicit full coefficient family, including the prime coefficient that
cancels the reciprocal slope. -/
theorem floorDilation_coefficients (p : ℕ) (hp : 0 < p) (s : Finset ℕ)
    (c : ℕ → ℝ) (hs : ∀ d ∈ s, 0 < d) :
    floorDilation p hp (∑ d ∈ s, c d • qResidue d) =
      (∑ d ∈ s, c d • qResidue (p * d)) -
        (∑ d ∈ s, c d / (d : ℝ)) • qResidue p := by
  calc
    _ = ∑ d ∈ s, (c d • qResidue (p * d) -
        (c d / (d : ℝ)) • qResidue p) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [map_smul, floorDilation_qResidue p d hp (hs d hd)]
      simp only [smul_sub, smul_smul, div_eq_mul_inv, one_mul]
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_smul]

def floorTrial (i p : ℕ) (hp : 0 < p) (f : QHilbert) (t : ℝ) : QHilbert :=
  headFirstMinimum i - t • floorDilation p hp f

theorem floorTrial_mem (i p : ℕ) (hp : 0 < p) (f : QHilbert)
    (hf : f ∈ divisorStage (oldPeriod i))
    (hperiod : p * oldPeriod i ∣ primorial (denseSchedule (i + 1) + 2)) (t : ℝ) :
    floorTrial i p hp f t ∈ divisorStage (primorial (denseSchedule (i + 1) + 2)) := by
  exact (divisorStage _).sub_mem
    (divisorStage_mono (primorial_dvd_primorial
      (Nat.add_le_add_right (denseSchedule_monotone (Nat.le_succ i)) 2))
      (minimumAt_mem _ _))
    ((divisorStage _).smul_mem _ (divisorStage_mono hperiod
      (floorDilation_mem_divisorStage (oldPeriod i) p (primorial_pos _) hp f hf)))

theorem floorTrial_head (i p : ℕ) (hi : 0 < i) (hp : 0 < p)
    (hpn : i + 2 < p) (f : QHilbert) (t : ℝ) (n : ℕ)
    (hn : 0 < n) (hni : n ≤ i + 2) : qSequence (floorTrial i p hp f t) n = 1 := by
  change qSequenceLinear (headFirstMinimum i - t • floorDilation p hp f) n = _
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change qSequence (headFirstMinimum i) n - t * qSequence (floorDilation p hp f) n = 1
  rw [floorDilation_sequence]
  simp only [Nat.div_eq_of_lt (show n < p by omega), qSequence_zero, mul_zero, sub_zero]
  exact minimumAt_head (denseSchedule i) (i + 2) (by dsimp [denseSchedule]; omega) n hn hni

/-- Exact complete-Q competitor identity for any full old-dictionary vector. -/
theorem floorTrial_completion (i p : ℕ) (hi : 0 < i) (hp : 0 < p)
    (hpn : i + 2 < p) (f : QHilbert) (hf : f ∈ divisorStage (oldPeriod i))
    (hperiod : p * oldPeriod i ∣ primorial (denseSchedule (i + 1) + 2)) (t : ℝ) :
    headFirstCost i - 2 * t * inner ℝ (headFirstMinimum i) (floorDilation p hp f) +
      t ^ 2 * ‖floorDilation p hp f‖ ^ 2 -
      (stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i) =
      ‖floorTrial i p hp f t - minimumAt (denseSchedule (i + 1)) (i + 2)‖ ^ 2 := by
  have hc := minimumAt_completion (denseSchedule (i + 1)) (i + 2)
    (by dsimp [denseSchedule]; omega) (floorTrial i p hp f t)
    (floorTrial_mem i p hp f hf hperiod t) (floorTrial_head i p hi hp hpn f t)
  have he : ‖floorTrial i p hp f t‖ ^ 2 = ‖headFirstMinimum i‖ ^ 2 -
      2 * t * inner ℝ (headFirstMinimum i) (floorDilation p hp f) +
      t ^ 2 * ‖floorDilation p hp f‖ ^ 2 := by
    simp only [floorTrial, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, inner_smul_right]
    ring
  have hn : ‖minimumAt (denseSchedule (i + 1)) (i + 2)‖ ^ 2 =
      stageEnergy denseSchedule (i + 1) := by simp only [stageEnergy, Nat.add_assoc]
  rw [he, hn] at hc
  unfold headFirstCost
  linarith

/-- A gain bound without a new-block inverse Gram matrix. -/
theorem floorTrial_step_le (i p : ℕ) (hi : 0 < i) (hp : 0 < p)
    (hpn : i + 2 < p) (f : QHilbert) (hf : f ∈ divisorStage (oldPeriod i))
    (hperiod : p * oldPeriod i ∣ primorial (denseSchedule (i + 1) + 2)) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i ≤
      headFirstCost i - (p : ℝ) *
        (inner ℝ (headFirstMinimum i) (floorDilation p hp f)) ^ 2 / ‖f‖ ^ 2 := by
  let s := inner ℝ (headFirstMinimum i) (floorDilation p hp f)
  let t := (p : ℝ) * s / ‖f‖ ^ 2
  have hc := floorTrial_completion i p hi hp hpn f hf hperiod t
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hquad : t ^ 2 * ‖floorDilation p hp f‖ ^ 2 ≤ (p : ℝ) * s ^ 2 / ‖f‖ ^ 2 := by
    calc
      _ ≤ t ^ 2 * (‖f‖ ^ 2 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left (floorDilation_norm_sq_le_sharp p hp f) (sq_nonneg t)
      _ = _ := by dsimp [t]; field_simp
  have ht : 2 * t * s = 2 * ((p : ℝ) * s ^ 2 / ‖f‖ ^ 2) := by dsimp [t]; ring
  change headFirstCost i - 2 * t * s + t ^ 2 * ‖floorDilation p hp f‖ ^ 2 -
      (stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i) = _ at hc
  rw [ht] at hc
  nlinarith [sq_nonneg ‖floorTrial i p hp f t - minimumAt (denseSchedule (i + 1)) (i + 2)‖]

theorem stageEnergy_pos (i : ℕ) : 0 < stageEnergy denseSchedule i := by
  have hh := minimumAt_head (denseSchedule i) (i + 1)
    (by dsimp [denseSchedule]; omega) 1 (by omega) (by omega)
  have hf : minimumAt (denseSchedule i) (i + 1) ≠ 0 := by
    intro hz
    rw [hz] at hh
    simp at hh
  exact sq_pos_of_pos (norm_pos_iff.mpr hf)

/-- A trial from the actual unrestricted old optimizer, using its full divisor
coefficient family rather than a prescribed prime-only subspace. -/
theorem selfDilation_step_le (i : ℕ) (hi : 0 < i)
    (hp : Nat.Prime (2 * i + 3)) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i ≤
      headFirstCost i - (2 * i + 3 : ℕ) *
        (inner ℝ (headFirstMinimum i)
          (floorDilation (2 * i + 3) (by omega)
            (minimumAt (denseSchedule i) (i + 1)))) ^ 2 / stageEnergy denseSchedule i := by
  apply floorTrial_step_le i (2 * i + 3) hi (by omega) (by omega)
    (minimumAt (denseSchedule i) (i + 1)) (minimumAt_mem _ _)
  rw [QCRTDivisorBlock.dense_primorial_eq_of_prime i hp]


end RiemannResearch.RH.QCRTFullFloorTrial

namespace RiemannResearch.RH.QCRTFullFloorTrial
open ZetaTwoHilbert QSquarefreeLatticePackets QCRTPeriodHeadBalance
open QSquarefreeEnergyTransitions QCRTPrimePairCertificate QCRTPrimeInnovation QFloorDilation

/-- The entire known head is subtracted from the norm denominator; the
remaining infinite tail defect and competitor loss both have favorable signs. -/
theorem floorTrial_step_le_head (i p H : ℕ) (hi : 0 < i) (hp : 0 < p)
    (hH : 0 < H) (hpn : i + 2 < p) (f : QHilbert)
    (hf : f ∈ divisorStage (oldPeriod i))
    (hhead : ∀ k, 0 < k → k ≤ H → qSequence f k = 1)
    (hperiod : p * oldPeriod i ∣ primorial (denseSchedule (i + 1) + 2)) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i ≤
      headFirstCost i - (inner ℝ (headFirstMinimum i) (floorDilation p hp f)) ^ 2 /
        (‖f‖ ^ 2 / (p : ℝ) - headBlockDefect p H) := by
  let s := inner ℝ (headFirstMinimum i) (floorDilation p hp f)
  let D := ‖f‖ ^ 2 / (p : ℝ) - headBlockDefect p H
  let t := s / D
  have hD : 0 < D := headAdjustedEnergy_pos p H hp hH f hhead
  have hc := floorTrial_completion i p hi hp hpn f hf hperiod t
  have hquad : t ^ 2 * ‖floorDilation p hp f‖ ^ 2 ≤ s ^ 2 / D := by
    calc
      _ ≤ t ^ 2 * D := mul_le_mul_of_nonneg_left
        (floorDilation_norm_sq_le_head p H hp f hhead) (sq_nonneg t)
      _ = _ := by dsimp [t]; field_simp
  have ht : 2 * t * s = 2 * (s ^ 2 / D) := by dsimp [t]; ring
  change headFirstCost i - 2 * t * s + t ^ 2 * ‖floorDilation p hp f‖ ^ 2 -
      (stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i) = _ at hc
  rw [ht] at hc
  nlinarith [sq_nonneg ‖floorTrial i p hp f t - minimumAt (denseSchedule (i + 1)) (i + 2)‖]

/-- Actual full-squarefree optimizer specialization with no separate spectral
or denominator-positivity hypothesis. -/
theorem selfDilation_step_le_head (i : ℕ) (hi : 0 < i)
    (hp : Nat.Prime (2 * i + 3)) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i ≤
      headFirstCost i -
        (inner ℝ (headFirstMinimum i)
          (floorDilation (2 * i + 3) (by omega)
            (minimumAt (denseSchedule i) (i + 1)))) ^ 2 /
          (stageEnergy denseSchedule i / (2 * i + 3 : ℕ) -
            headBlockDefect (2 * i + 3) (i + 1)) := by
  apply floorTrial_step_le_head i (2 * i + 3) (i + 1) hi (by omega) (by omega)
    (by omega) (minimumAt (denseSchedule i) (i + 1)) (minimumAt_mem _ _)
    (minimumAt_head (denseSchedule i) (i + 1) (by dsimp [denseSchedule]; omega))
  rw [QCRTDivisorBlock.dense_primorial_eq_of_prime i hp]

end RiemannResearch.RH.QCRTFullFloorTrial
