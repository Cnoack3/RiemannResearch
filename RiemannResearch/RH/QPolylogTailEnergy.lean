/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PolylogTailProfile
import RiemannResearch.Analysis.PSeriesTail
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

import RiemannResearch.Analysis.LogTailWeights
import RiemannResearch.Analysis.LogSquareTail

/-!
# Complete Q-tail bounds from physical polylogarithmic envelopes

Source: the user's two-residual paper argument, 26 October 2026.
The exact complete-tail identity is tail_energy_physical. The estimate
below applies to every QHilbert vector and uses the complete p-series
tail from Analysis/PSeriesTail, with constant 2 * C ^ 2/zetaTwo.

The physical envelope is an explicit hypothesis. This module does not
establish that hypothesis for a projection displacement.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QAnnihilatorTailEscape
open ZetaTwoHilbert ZetaTwoProbability QFiniteSupportDualCriterion
open RiemannResearch.Analysis.PolylogTail

theorem polylog_tail_energy_le
    (u : QHilbert) (C : ℝ) (_hC : 0 ≤ C) (m N : ℕ) (hN : 1 ≤ N)
    (hk : ((4 * m : ℕ) : ℝ) ≤ 6 + Real.log (N : ℝ))
    (hb : ∀ n : ℕ, N < n →
      |qSequence u n| ≤ C * (6 + Real.log (n : ℝ)) ^ m) :
    ‖tail N u‖ ^ 2 ≤ (2 * C ^ 2/zetaTwo) *
      (6 + Real.log (N : ℝ)) ^ (2 * m) / (N : ℝ) := by
  have hz := zetaTwo_pos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hLN : 0 ≤ 6 + Real.log (N : ℝ) := by linarith [Real.log_nonneg hN1]
  let K : ℝ := (C ^ 2/zetaTwo) *
    ((6 + Real.log (N : ℝ)) ^ (2 * m) / Real.sqrt (N : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsQ : Summable (fun j : ℕ => positiveQWeight (j + N + 1) *
      qSequence u (j + N + 1)^2) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (N + 1)).mpr (qSequence_square_summable u)
  have hsP : Summable (fun j : ℕ => ((j + N + 1 : ℕ) : ℝ)^(-(3/2 : ℝ))) := by
    have hp : Summable (fun n : ℕ => (n : ℝ)^(-(3/2 : ℝ))) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (N + 1)).mpr hp
  have hterm (j : ℕ) : positiveQWeight (j + N + 1) * qSequence u (j + N + 1)^2 ≤
      K * ((j + N + 1 : ℕ) : ℝ)^(-(3/2 : ℝ)) := by
    let n : ℕ := j + N + 1
    have hnN : N < n := by dsimp [n]; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsq : qSequence u n ^ 2 ≤ C ^ 2 * (6 + Real.log (n : ℝ)) ^ (2 * m) := by
      have hh := mul_self_le_mul_self (abs_nonneg (qSequence u n)) (hb n hnN)
      have he : (C * (6 + Real.log (n : ℝ)) ^ m)^2 =
          C ^ 2 * (6 + Real.log (n : ℝ)) ^ (2 * m) := by
        rw [mul_pow, ← pow_mul]
        congr 2
        omega
      nlinarith [sq_abs (qSequence u n)]
    have hw := mul_le_mul_of_nonneg_left hsq (positiveQWeight_nonneg n)
    have hp := log_pow_div_sq_le m hN1
      (show (N : ℝ) ≤ (n : ℝ) by exact_mod_cast hnN.le) hk
    calc
      _ ≤ positiveQWeight n * (C ^ 2 * (6 + Real.log (n : ℝ)) ^ (2 * m)) := hw
      _ = (C ^ 2/zetaTwo) * ((6 + Real.log (n : ℝ)) ^ (2 * m)/(n : ℝ)^2) := by
        simp only [positiveQWeight]
        ring
      _ ≤ (C ^ 2/zetaTwo) *
          (((6 + Real.log (N : ℝ)) ^ (2 * m)/Real.sqrt (N : ℝ)) *
            (n : ℝ)^(-(3/2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by dsimp [K, n]; ring
  have ht : (∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ)^(-(3/2 : ℝ))) ≤
      (N : ℝ)^(-(1/2 : ℝ))/(1/2 : ℝ) := by
    have h := Real.tsum_nat_rpow_tail_le (p := (3/2 : ℝ)) (by norm_num) hN
    convert h using 1 <;> norm_num
  rw [tail_energy_physical]
  calc
    _ ≤ ∑' j : ℕ, K * ((j + N + 1 : ℕ) : ℝ)^(-(3/2 : ℝ)) :=
      hsQ.tsum_le_tsum hterm (hsP.mul_left K)
    _ = K * ∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ)^(-(3/2 : ℝ)) := tsum_mul_left
    _ ≤ K * ((N : ℝ)^(-(1/2 : ℝ))/(1/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left ht hK
    _ = _ := by
      dsimp [K]
      rw [rpow_neg_half hN0]
      field_simp [hN0.ne', (Real.sqrt_pos.mpr hN0).ne', zetaTwo_pos.ne']
      nlinarith [Real.sq_sqrt hN0.le]

theorem eventually_polylog_scaled_tail_le
    (u : QHilbert) (C : ℝ) (hC : 0 ≤ C) (m : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop,
      |qSequence u n| ≤ C * (6 + Real.log (n : ℝ)) ^ m) :
    ∀ᶠ N : ℕ in atTop, ((N : ℝ)/(6 + Real.log (N : ℝ)) ^ (2 * m)) *
      ‖tail N u‖ ^ 2 ≤ 2 * C ^ 2/zetaTwo := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 hb
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (max M 1),
    ht.eventually (eventually_ge_atTop (((4 * m : ℕ) : ℝ)-6))] with N hN hL
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLN : 0 < 6 + Real.log (N : ℝ) := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    linarith [Real.log_nonneg hNreal]
  have h := polylog_tail_energy_le u C hC m N hN1 (by linarith)
    (fun n hn => hM n (by omega))
  have hw : 0 ≤ (N : ℝ)/(6 + Real.log (N : ℝ)) ^ (2 * m) := by positivity
  have hs := mul_le_mul_of_nonneg_left h hw
  calc
    _ ≤ ((N : ℝ)/(6 + Real.log (N : ℝ)) ^ (2 * m)) *
        ((2 * C ^ 2/zetaTwo) * (6 + Real.log (N : ℝ)) ^ (2 * m) / (N : ℝ)) := hs
    _ = _ := by
      field_simp [hN0.ne', (pow_pos hLN (2 * m)).ne']

end RiemannResearch.RH.QAnnihilatorTailEscape

/-!
## Monotone weighted energies and finite-head consumers

Source: the user's squarefree moving-head continuation, 26 October 2026.
These complete-energy estimates complement the sharp eventual tail bound
above. The monotone profile is designed for cofinal finite-head budgets.
-/

namespace RiemannResearch.RH.QPolylogTailEnergy
open ZetaTwoHilbert ZetaTwoProbability QAnnihilatorTailEscape
open RiemannResearch.Analysis RiemannResearch.Analysis.LogTailWeights

def polylogWeightedEnergyTerm (k : ℕ) (u : QHilbert) (n : ℕ) : ℝ :=
  polylogTailProfile k n * positiveQWeight n * qSequence u n ^ 2

theorem polylogWeightedEnergyTerm_nonneg (k : ℕ) (u : QHilbert) (n : ℕ) :
    0 ≤ polylogWeightedEnergyTerm k u n :=
  mul_nonneg (mul_nonneg (polylogTailProfile_nonneg k n)
    (positiveQWeight_nonneg n)) (sq_nonneg _)

/-- The exact positive-site physical expression for the weighted energy. -/
theorem polylogWeightedEnergyTerm_eq (k n : ℕ) (u : QHilbert) (hn : 0 < n) :
    polylogWeightedEnergyTerm k u n = qSequence u n ^ 2 /
      (zetaTwo * (n : ℝ) * ((k : ℝ) + 6 + Real.log (n : ℝ)) ^ k) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < (k : ℝ) + 6 + Real.log (n : ℝ) := by
    have hk := Nat.cast_nonneg (α := ℝ) k
    linarith [Real.log_nonneg hn1]
  unfold polylogWeightedEnergyTerm positiveQWeight
  rw [polylogTailProfile_eq]
  field_simp [ne_of_gt hn0, ne_of_gt hL, ne_of_gt zetaTwo_pos] <;> ring

/-- A single physical envelope value gives its complete-energy majorant. -/
theorem polylogWeightedEnergyTerm_le_log_square
    (u : QHilbert) (m n : ℕ) (C : ℝ)
    (hu : |qSequence u n| ≤ C*(6+Real.log (n : ℝ))^m) :
    polylogWeightedEnergyTerm (2*m+2) u n ≤
      (C^2/zetaTwo) * (1 / ((n : ℝ)*(6+Real.log (n : ℝ))^2)) := by
  by_cases hn : n = 0
  · simp [hn, polylogWeightedEnergyTerm, polylogTailProfile_eq, qSequence]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hL : 0 < 6+Real.log (n : ℝ) := by linarith [Real.log_nonneg hn1]
  have hsq : qSequence u n ^ 2 ≤ C^2*(6+Real.log (n : ℝ))^(2*m) := by
    have h := mul_self_le_mul_self (abs_nonneg (qSequence u n)) hu
    simpa only [← pow_two, sq_abs, mul_pow, ← pow_mul, Nat.mul_comm m 2] using h
  have hw := polylogTailProfile_le_logWeight (2*m+2) n
  calc
    polylogWeightedEnergyTerm (2*m+2) u n
        ≤ polylogTailProfile (2*m+2) n * positiveQWeight n *
          (C^2*(6+Real.log (n : ℝ))^(2*m)) :=
      mul_le_mul_of_nonneg_left hsq
        (mul_nonneg (polylogTailProfile_nonneg _ _) (positiveQWeight_nonneg _))
    _ ≤ logWeight (2*m+2) n * positiveQWeight n *
          (C^2*(6+Real.log (n : ℝ))^(2*m)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hw (positiveQWeight_nonneg n)) (by positivity)
    _ = _ := by
      unfold logWeight positiveQWeight
      rw [pow_add]
      field_simp [ne_of_gt hn0, ne_of_gt hL, ne_of_gt zetaTwo_pos]
      <;> ring

/-- A polylogarithmic physical envelope supplies an absolutely summable
weighted energy, using two additional logarithmic powers. -/
theorem polylogWeightedEnergyTerm_summable (u : QHilbert) (m : ℕ)
    (C : ℝ) (_hC : 0 ≤ C)
    (hu : ∀ n : ℕ, |qSequence u n| ≤ C*(6+Real.log (n : ℝ))^m) :
    Summable (polylogWeightedEnergyTerm (2*m+2) u) := by
  have hs : Summable (fun n : ℕ =>
      1 / ((n : ℝ)*(6+Real.log (n : ℝ))^2)) := by
    simpa only [Real.rpow_two] using summable_shifted_log_square
  exact Summable.of_nonneg_of_le
    (polylogWeightedEnergyTerm_nonneg (2*m+2) u)
    (fun n => polylogWeightedEnergyTerm_le_log_square u m n C (hu n))
    (hs.mul_left (C^2/zetaTwo))

/-- The entire Q tail is bounded by a single weighted infinite energy.
The monotone profile is compared at every physical tail coordinate. -/
theorem profile_mul_tail_energy_le (k N : ℕ) (u : QHilbert)
    (hs : Summable (polylogWeightedEnergyTerm k u)) :
    polylogTailProfile k N * ‖tail N u‖^2 ≤
      ∑' n : ℕ, polylogWeightedEnergyTerm k u n := by
  have hq : Summable (fun j : ℕ => positiveQWeight (j+(N+1)) *
      qSequence u (j+(N+1))^2) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => positiveQWeight n * qSequence u n ^ 2)
      (N+1)).mpr (qSequence_square_summable u)
  have ht : Summable (fun j : ℕ => polylogWeightedEnergyTerm k u (j+(N+1))) :=
    (summable_nat_add_iff
      (f := polylogWeightedEnergyTerm k u) (N+1)).mpr hs
  have hb (j : ℕ) : polylogTailProfile k N *
      (positiveQWeight (j+(N+1)) * qSequence u (j+(N+1))^2) ≤
      polylogWeightedEnergyTerm k u (j+(N+1)) := by
    have hp := polylogTailProfile_monotone k (by omega : N ≤ j+(N+1))
    have h := mul_le_mul_of_nonneg_right hp
      (mul_nonneg (positiveQWeight_nonneg (j + (N + 1)))
        (sq_nonneg (qSequence u (j + (N + 1)))))
    simpa only [polylogWeightedEnergyTerm, mul_assoc] using h
  have hsum := (hq.mul_left (polylogTailProfile k N)).tsum_le_tsum hb ht
  rw [tsum_mul_left] at hsum
  have he := hs.sum_add_tsum_nat_add (N+1)
  have hhead : 0 ≤ ∑ n ∈ Finset.range (N+1), polylogWeightedEnergyTerm k u n :=
    Finset.sum_nonneg (fun n _ => polylogWeightedEnergyTerm_nonneg k u n)
  rw [tail_energy_physical]
  simp only [Nat.add_assoc] at hsum ⊢
  linarith

/-- A complete-tail bound with some finite constant follows from any fixed
integer polylogarithmic physical envelope. -/
theorem exists_log_scaled_tail_bound_of_polylog (u : QHilbert) (m : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ n : ℕ, |qSequence u n| ≤ C*(6+Real.log (n : ℝ))^m) :
    ∃ D : ℝ, ∀ N : ℕ, logWeight (2*m+2) N * ‖tail N u‖^2 ≤ D := by
  let k := 2*m+2
  have hs := polylogWeightedEnergyTerm_summable u m C hC hu
  refine ⟨((k : ℝ)+6)^k * (∑' n : ℕ, polylogWeightedEnergyTerm k u n), ?_⟩
  intro N
  have h1 := mul_le_mul_of_nonneg_right
    (logWeight_le_polylogTailProfile k N) (sq_nonneg ‖tail N u‖)
  have h2 := mul_le_mul_of_nonneg_left (profile_mul_tail_energy_le k N u hs)
    (pow_nonneg (by positivity : 0 ≤ (k : ℝ)+6) k)
  dsimp [k] at *
  nlinarith

end RiemannResearch.RH.QPolylogTailEnergy
