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
