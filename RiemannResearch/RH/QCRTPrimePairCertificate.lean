/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTPrimePairTrial
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Actual moving-optimizer certificates from an explicit conductor pair.
Source: the user-provided handoff of 30 October 2026, Section 4.2, and the
direct minimum-norm competitor argument. Full remainder squares are retained.
No all-stage or cofinal arithmetic growth provider is asserted. -/
noncomputable section
namespace RiemannResearch.RH.QCRTPrimePairCertificate
open ZetaTwoHilbert QSquarefreeLatticePackets QCRTPeriodHeadBalance
open QSquarefreeEnergyTransitions QCRTPrimePairTrial

/-- The actual OLD-dictionary minimum with the next head already imposed. -/
def headFirstMinimum (i : ℕ) : QHilbert :=
  minimumAt (denseSchedule i) (i + 2)

def headFirstCost (i : ℕ) : ℝ :=
  ‖headFirstMinimum i‖ ^ 2 - stageEnergy denseSchedule i

def pairSource (i p : ℕ) : ℝ :=
  inner ℝ (headFirstMinimum i) (primePair p)

def pairTrial (i p : ℕ) (t : ℝ) : QHilbert :=
  headFirstMinimum i - t • primePair p

theorem headFirstCost_nonneg (i : ℕ) : 0 ≤ headFirstCost i := by
  have h := minimumAt_head_cost (denseSchedule i) (i + 1) (i + 2) (by omega)
  change ‖headFirstMinimum i‖ ^ 2 =
    stageEnergy denseSchedule i +
      ‖headFirstMinimum i - minimumAt (denseSchedule i) (i + 1)‖ ^ 2 at h
  unfold headFirstCost
  nlinarith [sq_nonneg ‖headFirstMinimum i - minimumAt (denseSchedule i) (i + 1)‖]

theorem pairTrial_mem (i p : ℕ) (t : ℝ)
    (hpL : p ∣ primorial (denseSchedule (i + 1) + 2))
    (h2pL : 2 * p ∣ primorial (denseSchedule (i + 1) + 2)) :
    pairTrial i p t ∈ divisorStage (primorial (denseSchedule (i + 1) + 2)) := by
  exact (divisorStage _).sub_mem
    (divisorStage_mono (primorial_dvd_primorial
      (Nat.add_le_add_right (denseSchedule_monotone (Nat.le_succ i)) 2))
      (minimumAt_mem _ _))
    ((divisorStage _).smul_mem _ (primePair_mem_divisorStage p _ hpL h2pL))

theorem pairTrial_head (i p : ℕ) (hi : 0 < i) (hp : 0 < p)
    (hpn : i + 2 < p) (t : ℝ) (n : ℕ) (hn : 0 < n) (hni : n ≤ i + 2) :
    qSequence (pairTrial i p t) n = 1 := by
  change qSequenceLinear (headFirstMinimum i - t • primePair p) n = _
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change qSequence (headFirstMinimum i) n - t * qSequence (primePair p) n = 1
  rw [primePair_head p n hp (by omega)]
  simpa only [mul_zero, sub_zero, headFirstMinimum] using
    minimumAt_head (denseSchedule i) (i + 2) (by dsimp [denseSchedule]; omega) n hn hni

/-- Full finite-stage arithmetic identity, including the exact competitor loss. -/
theorem primePair_completion (i p : ℕ) (hi : 0 < i) (hp : 0 < p)
    (hpn : i + 2 < p)
    (hpL : p ∣ primorial (denseSchedule (i + 1) + 2))
    (h2pL : 2 * p ∣ primorial (denseSchedule (i + 1) + 2)) (t : ℝ) :
    headFirstCost i - 2 * t * pairSource i p + t ^ 2 * ‖primePair p‖ ^ 2 -
      (stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i) =
      ‖pairTrial i p t - minimumAt (denseSchedule (i + 1)) (i + 2)‖ ^ 2 := by
  have hc := minimumAt_completion (denseSchedule (i + 1)) (i + 2)
    (by dsimp [denseSchedule]; omega) (pairTrial i p t)
    (pairTrial_mem i p t hpL h2pL) (pairTrial_head i p hi hp hpn t)
  have he : ‖pairTrial i p t‖ ^ 2 = ‖headFirstMinimum i‖ ^ 2 -
      2 * t * pairSource i p + t ^ 2 * ‖primePair p‖ ^ 2 := by
    simp only [pairTrial, pairSource, norm_sub_sq_real, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right]
    ring
  have hn : ‖minimumAt (denseSchedule (i + 1)) (i + 2)‖ ^ 2 =
      stageEnergy denseSchedule (i + 1) := by
    simp only [stageEnergy, Nat.add_assoc]
  rw [he, hn] at hc
  unfold headFirstCost
  linarith

/-- Explicit cancellation using the complete energy bound 3/(4p).
The actual old-dictionary head-first optimizer remains in the signed source. -/
theorem primePair_step_le_cost_sub_source_sq (i p : ℕ) (hi : 0 < i)
    (hp : 0 < p) (hpn : i + 2 < p)
    (hpL : p ∣ primorial (denseSchedule (i + 1) + 2))
    (h2pL : 2 * p ∣ primorial (denseSchedule (i + 1) + 2)) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i ≤
      headFirstCost i - (4 / 3 : ℝ) * (p : ℝ) * pairSource i p ^ 2 := by
  have hc := primePair_completion i p hi hp hpn hpL h2pL
    ((4 / 3 : ℝ) * (p : ℝ) * pairSource i p)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hquad : ((4 / 3 : ℝ) * (p : ℝ) * pairSource i p) ^ 2 * ‖primePair p‖ ^ 2 ≤
      (4 / 3 : ℝ) * (p : ℝ) * pairSource i p ^ 2 := by
    calc
      _ ≤ ((4 / 3 : ℝ) * (p : ℝ) * pairSource i p) ^ 2 * (3 / (4 * (p : ℝ))) :=
        mul_le_mul_of_nonneg_left (primePair_norm_sq_le p hp) (sq_nonneg _)
      _ = _ := by field_simp [hpR]
  nlinarith [sq_nonneg ‖pairTrial i p ((4 / 3 : ℝ) * (p : ℝ) * pairSource i p) -
    minimumAt (denseSchedule (i + 1)) (i + 2)‖]




theorem dense_new_prime_pair_bound (i : ℕ) (hi : 0 < i)
    (hp : Nat.Prime (2 * i + 3)) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i ≤
      headFirstCost i - (4 / 3 : ℝ) * (2 * i + 3 : ℕ) * pairSource i (2 * i + 3) ^ 2 := by
  have hpL : 2 * i + 3 ∣ primorial (denseSchedule (i + 1) + 2) :=
    dvd_trans hp.squarefree.dvd_primorial
      (primorial_dvd_primorial (by dsimp [denseSchedule]; omega))
  have h2L : 2 ∣ primorial (denseSchedule (i + 1) + 2) :=
    dvd_trans Nat.prime_two.squarefree.dvd_primorial
      (primorial_dvd_primorial (by dsimp [denseSchedule]; omega))
  have hcop : Nat.Coprime 2 (2 * i + 3) := by
    exact Nat.coprime_two_left.mpr ⟨i + 1, by omega⟩
  exact primePair_step_le_cost_sub_source_sq i (2 * i + 3) hi (by omega)
    (by omega) hpL (hcop.mul_dvd_of_dvd_of_dvd h2L hpL)
end RiemannResearch.RH.QCRTPrimePairCertificate
