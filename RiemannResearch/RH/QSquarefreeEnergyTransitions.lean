/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTMinimumHeadCost
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeHeadStep
import RiemannResearch.RH.QSquarefreeFiniteDualClosure
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic bounds for actual squarefree minimum-energy transitions

Source: user-provided Minimum Energy Optimizer Research Agenda, 29 October
2026, Sections 5--7. This reuses the exact complete-energy capacity formula
in QCRTMinimumHeadCost. The explicit schedule uses primorial(2H), and
Bertrand's theorem discharges every nearby-anchor existence condition.
Nonsquarefree sites contribute zero extension cost by radical compatibility.
All period gains and the full infinite Q tail are retained. The moving
prediction budget is explicit; no uniform bound on it is asserted.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeEnergyTransitions
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets
open QSquarefreeAffineHead QCRTPeriodHeadBalance QSquarefreeHeadStep
open QCRTMinimumHeadCost
open QSquarefreeFiniteDualClosure SquarefreeRadicalDifference
open UniqueFactorizationMonoid

/-- A nonsquarefree physical site imposes no new constant-head constraint. -/
theorem nonsquarefree_next_value (n : ℕ) (hn : 2 ≤ n)
    (hns : ¬ Squarefree n) (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan) (a : ℝ)
    (hh : ∀ k, 0 < k → k < n → qSequence F k = a) :
    qSequence F n = a := by
  have hr2 : 2 ≤ radical n := Nat.two_le_radical_iff.mpr hn
  have hrle : radical n ≤ n := Nat.radical_le_self_iff.mpr (by omega)
  have hrlt : radical n < n := by
    by_contra h
    have he : radical n = n := by omega
    exact hns (he ▸ squarefree_radical)
  have he := legal_le_radicalCompatible hF n hn
  change qSequence F n - qSequence F (n - 1) =
    qSequence F (radical n) - qSequence F (radical n - 1) at he
  rw [hh (n - 1) (by omega) (by omega),
    hh (radical n) (by omega) hrlt,
    hh (radical n - 1) (by omega) (by omega)] at he
  linarith

/-- The actual complete-energy minima satisfy the nearby-anchor bound. -/
theorem minimumAt_single_head_near_anchor_bound (j n r : ℕ) (hn : 1 < n)
    (hnj : n ≤ j + 1) (hnL : n ∣ primorial (j + 2))
    (hr : r ∈ conductors (primorial (j + 2))) (hrn : n < r)
    (hrnear : r ≤ 2 * n) :
    ‖minimumAt j n‖ ^ 2 ≤ ‖minimumAt j (n - 1)‖ ^ 2 +
      (1 - qSequence (minimumAt j (n - 1)) n) ^ 2 *
        ((1 / zetaTwo) * (4 / (n - 1 : ℕ))) := by
  have hratio : (r : ℝ) / n ≤ 2 := by
    apply (div_le_iff₀
      (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)).mpr
    exact_mod_cast hrnear
  have hsq : ((r : ℝ) / n) ^ 2 ≤ 4 := by
    nlinarith [show (0 : ℝ) ≤ (r : ℝ) / n by positivity]
  have henergy := (compensatedResidue_energy_le n r hn hrn.le).trans
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hsq (Nat.cast_nonneg (n - 1)))
      (one_div_nonneg.mpr zetaTwo_pos.le))
  have hinv := (inverse_stepCapacity_le_trial_energy n (primorial (j + 2)) r
    hn (primorial_pos _) hnL hr hrn).trans henergy
  rw [minimumAt_single_head_cost j n r hn hnj hnL hr hrn]
  apply add_le_add le_rfl
  calc
    _ = (1 - qSequence (minimumAt j (n - 1)) n) ^ 2 *
        (1 / stepCapacity n (primorial (j + 2)) r hr) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hinv (sq_nonneg _)

/-- Dependent physical constraints change neither the minimum nor its vector. -/
theorem minimumAt_eq_of_nonsquarefree (j n : ℕ) (hn : 2 ≤ n)
    (hnj : n ≤ j + 1) (hns : ¬ Squarefree n) :
    minimumAt j n = minimumAt j (n - 1) := by
  have hh : ∀ k, 0 < k → k ≤ n → qSequence (minimumAt j (n - 1)) k = 1 := by
    intro k hk hkn
    by_cases he : k = n
    · subst k
      exact nonsquarefree_next_value n hn hns (minimumAt j (n - 1))
        (minimumAt_legal j (n - 1)) 1 (fun k hk hkn =>
          minimumAt_head j (n - 1) (by omega) k hk (by omega))
    · exact minimumAt_head j (n - 1) (by omega) k hk (by omega)
  have hc := minimumAt_completion j n hnj (minimumAt j (n - 1))
    (minimumAt_mem j (n - 1)) hh
  have hs := minimumAt_head_cost j (n - 1) n (by omega)
  have hz : ‖minimumAt j n - minimumAt j (n - 1)‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖minimumAt j (n - 1) - minimumAt j n‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

theorem headCost_eq_zero_of_nonsquarefree (σ : ℕ → ℕ) (i : ℕ)
    (hhead : i + 1 ≤ σ (i + 1)) (hns : ¬ Squarefree (i + 2)) :
    headCost σ i = 0 := by
  have he := minimumAt_eq_of_nonsquarefree (σ (i + 1)) (i + 2)
    (by omega) (by omega) hns
  simp only [show i + 2 - 1 = i + 1 by omega] at he
  simp only [headCost, he, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- The gain is retained in the actual signed recurrence even when a simple
two-conductor trial is used to bound extension cost. -/
theorem stageEnergy_step_near_anchor_bound (σ : ℕ → ℕ) (hσ : Monotone σ)
    (hhead : ∀ i, i ≤ σ i) (i r : ℕ)
    (hnL : i + 2 ∣ primorial (σ (i + 1) + 2))
    (hr : r ∈ conductors (primorial (σ (i + 1) + 2)))
    (hrn : i + 2 < r) (hrnear : r ≤ 2 * (i + 2)) :
    stageEnergy σ (i + 1) ≤ stageEnergy σ i - periodGain σ i +
      (1 - qSequence (minimumAt (σ (i + 1)) (i + 1)) (i + 2)) ^ 2 *
        ((1 / zetaTwo) * (4 / (i + 1 : ℕ))) := by
  have hb := minimumAt_single_head_near_anchor_bound (σ (i + 1)) (i + 2) r
    (by omega) (by have := hhead (i + 1); omega) hnL hr hrn hrnear
  simp only [show i + 2 - 1 = i + 1 by omega] at hb
  have hc := minimumAt_head_cost (σ (i + 1)) (i + 1) (i + 2) (by omega)
  rw [stageEnergy_step σ hσ hhead]
  have hb' : headCost σ i ≤
      (1 - qSequence (minimumAt (σ (i + 1)) (i + 1)) (i + 2)) ^ 2 *
        ((1 / zetaTwo) * (4 / (i + 1 : ℕ))) := by
    change ‖minimumAt (σ (i + 1)) (i + 2) -
      minimumAt (σ (i + 1)) (i + 1)‖ ^ 2 ≤ _
    linarith only [hb, hc]
  exact add_le_add le_rfl hb'

/-- Head H=i+1 uses precisely the divisor dictionary of primorial(2H). -/
def denseSchedule (i : ℕ) : ℕ := 2 * i

theorem denseSchedule_monotone : Monotone denseSchedule := by
  intro i j hij
  dsimp [denseSchedule]
  omega

theorem denseSchedule_head (i : ℕ) : i ≤ denseSchedule i := by
  dsimp [denseSchedule]
  omega

/-- The moving next-site mismatch after enlarging the actual dictionary. -/
def nextMismatch (i : ℕ) : ℝ :=
  1 - qSequence (minimumAt (denseSchedule (i + 1)) (i + 1)) (i + 2)

theorem nextMismatch_eq_zero_of_nonsquarefree (i : ℕ)
    (hns : ¬ Squarefree (i + 2)) : nextMismatch i = 0 := by
  have he := nonsquarefree_next_value (i + 2) (by omega) hns
    (minimumAt (denseSchedule (i + 1)) (i + 1))
    (minimumAt_legal _ _) 1 (fun k hk hki =>
      minimumAt_head _ _ (by dsimp [denseSchedule]; omega) k hk (by omega))
  simp only [nextMismatch, he, sub_self]

/-- A complete arithmetic cost bound with every existence premise discharged.
Only the actual moving mismatch remains for future estimates. -/
theorem dense_headCost_bound (i : ℕ) :
    headCost denseSchedule i ≤ nextMismatch i ^ 2 *
      ((1 / zetaTwo) * (4 / (i + 1 : ℕ))) := by
  by_cases hsf : Squarefree (i + 2)
  · obtain ⟨r, hrprime, hrlower, hrupper⟩ :=
      Nat.exists_prime_lt_and_le_two_mul (i + 2) (by omega)
    have hnL : i + 2 ∣ primorial (denseSchedule (i + 1) + 2) :=
      dvd_trans hsf.dvd_primorial
        (primorial_dvd_primorial (by dsimp [denseSchedule]; omega))
    have hrL : r ∣ primorial (denseSchedule (i + 1) + 2) :=
      dvd_trans hrprime.squarefree.dvd_primorial
        (primorial_dvd_primorial (by dsimp [denseSchedule]; omega))
    have hr : r ∈ conductors (primorial (denseSchedule (i + 1) + 2)) :=
      Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hrL, primorial_ne_zero _⟩, by omega⟩
    have hb := minimumAt_single_head_near_anchor_bound
      (denseSchedule (i + 1)) (i + 2) r (by omega)
      (by dsimp [denseSchedule]; omega) hnL hr hrlower hrupper
    simp only [show i + 2 - 1 = i + 1 by omega] at hb
    have hc := minimumAt_head_cost (denseSchedule (i + 1)) (i + 1) (i + 2)
      (by omega)
    change ‖minimumAt (denseSchedule (i + 1)) (i + 2) -
      minimumAt (denseSchedule (i + 1)) (i + 1)‖ ^ 2 ≤
      (1 - qSequence (minimumAt (denseSchedule (i + 1)) (i + 1)) (i + 2)) ^ 2 *
        ((1 / zetaTwo) * (4 / (i + 1 : ℕ)))
    linarith only [hb, hc]
  · rw [headCost_eq_zero_of_nonsquarefree denseSchedule i
      (denseSchedule_head (i + 1)) hsf]
    rw [nextMismatch_eq_zero_of_nonsquarefree i hsf]
    simp

open scoped BigOperators

def predictionBudget (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, nextMismatch i ^ 2 / (i + 1 : ℕ)

/-- Telescoped actual costs retain all period-enlargement gains. -/
theorem dense_energy_signed_bound (N : ℕ) :
    stageEnergy denseSchedule N ≤ stageEnergy denseSchedule 0 +
      (4 / zetaTwo) * predictionBudget N -
        ∑ i ∈ Finset.range N, periodGain denseSchedule i := by
  have hp (i : ℕ) : headCost denseSchedule i ≤
      (4 / zetaTwo) * (nextMismatch i ^ 2 / (i + 1 : ℕ)) := by
    convert dense_headCost_bound i using 1
    ring
  have hs := Finset.sum_le_sum (s := Finset.range N)
    (fun i _ => sub_le_sub_right (hp i) (periodGain denseSchedule i))
  calc
    stageEnergy denseSchedule N = stageEnergy denseSchedule 0 +
        ∑ i ∈ Finset.range N, (headCost denseSchedule i - periodGain denseSchedule i) :=
      stageEnergy_telescope denseSchedule denseSchedule_monotone denseSchedule_head N
    _ ≤ stageEnergy denseSchedule 0 + ∑ i ∈ Finset.range N,
        ((4 / zetaTwo) * (nextMismatch i ^ 2 / (i + 1 : ℕ)) -
          periodGain denseSchedule i) := add_le_add le_rfl hs
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      dsimp [predictionBudget]
      ring

theorem dense_energy_le_predictionBudget (N : ℕ) :
    stageEnergy denseSchedule N ≤ stageEnergy denseSchedule 0 +
      (4 / zetaTwo) * predictionBudget N := by
  have h := dense_energy_signed_bound N
  have hg : 0 ≤ ∑ i ∈ Finset.range N, periodGain denseSchedule i :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith


theorem predictionBudget_nonneg (N : ℕ) : 0 ≤ predictionBudget N :=
  Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

/-- A bounded moving prediction supplies a logarithmic, rather than bounded,
energy budget. The prediction bound is not asserted. -/
theorem predictionBudget_le_harmonic (B : ℝ) (hB : 0 ≤ B)
    (hprediction : ∀ i, |nextMismatch i| ≤ B) (N : ℕ) :
    predictionBudget N ≤ B ^ 2 * (harmonic N : ℝ) := by
  calc
    predictionBudget N ≤ ∑ i ∈ Finset.range N, B ^ 2 / (i + 1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hB] using hprediction i)
    _ = B ^ 2 * (harmonic N : ℝ) := by
      simp [harmonic, Finset.mul_sum, div_eq_mul_inv]

theorem predictionBudget_le_log (B : ℝ) (hB : 0 ≤ B)
    (hprediction : ∀ i, |nextMismatch i| ≤ B) (N : ℕ) :
    predictionBudget N ≤ B ^ 2 * (1 + Real.log (N : ℝ)) :=
  (predictionBudget_le_harmonic B hB hprediction N).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (sq_nonneg B))

end RiemannResearch.RH.QSquarefreeEnergyTransitions
