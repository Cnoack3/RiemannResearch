/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoCRTReciprocalEnergy
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ParetoCRTReciprocalEnergy
import RiemannResearch.RH.QResidueConditional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact first-period Q energy and its complete periodic tail

Source: user-provided squarefree CRT research agenda, 16--19 October 2026.
This module retains the exact tail after the first period and bounds it above
and below by the unweighted period energy divided by the period squared.
Only the complete arithmetic progression series is used. No special-function
asymptotic estimate or uniform RH-strength energy hypothesis is assumed.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.ZetaTwoProbability
open Pareto ZetaTwoHilbert

theorem residuePowerWeight_antitone_anchor (s : ℕ) {L a b : ℝ}
    (hL : 0 < L) (ha : 0 < a) (hab : a ≤ b) :
    residuePowerWeight s L b ≤ residuePowerWeight s L a := by
  apply Summable.tsum_le_tsum _
    (residuePowerWeight_summable s hL (ha.trans_le hab))
    (residuePowerWeight_summable s hL ha)
  intro j
  apply one_div_le_one_div_of_le (by have := zetaTwo_pos; positivity)
  apply mul_le_mul_of_nonneg_left _ zetaTwo_pos.le
  have hbase : a + (j : ℝ) * L ≤ b + (j : ℝ) * L := by linarith
  exact pow_le_pow_left₀ (by positivity : 0 ≤ a + (j : ℝ) * L) hbase (s + 2)

/-- Every shifted progression mass lies between its two endpoint masses.
The constants describe the entire infinite tail, not a truncated sum. -/
theorem residueSquareWeight_tail_bounds (L : ℕ) (hL : 0 < L)
    {a : ℝ} (ha : 0 < a) (haL : a ≤ L) :
    (1 - 1 / zetaTwo) / (L : ℝ)^2 ≤ residuePowerWeight 0 L (a + L) ∧
      residuePowerWeight 0 L (a + L) ≤ 1 / (L : ℝ)^2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hzero := QResidueConditional.residuePowerWeight_zeroClass L
  have hshift := residuePowerWeight_shift 0 hLR hLR
  have he : residuePowerWeight 0 L ((L : ℝ) + L) =
      (1 - 1 / zetaTwo) / (L : ℝ)^2 := by
    rw [hzero] at hshift
    have halg : (1 - 1 / zetaTwo) / (L : ℝ)^2 =
        1 / (L : ℝ)^2 - 1 / (zetaTwo * (L : ℝ)^2) := by ring
    rw [halg]
    simp only [Nat.zero_add] at hshift
    linarith
  constructor
  · rw [← he]
    exact residuePowerWeight_antitone_anchor 0 (a := a + L) (b := (L : ℝ) + L)
      hLR (by positivity) (by linarith)
  · rw [← hzero]
    exact residuePowerWeight_antitone_anchor 0 (a := (L : ℝ)) (b := a + L)
      hLR hLR (by linarith)

/-- Unweighted square energy in the physical positive representatives. -/
def periodSquareEnergy (L : ℕ) (R : ℕ → ℝ) : ℝ :=
  ∑ a : Fin L, R (a.val + 1)^2

/-- Exact complete contribution of all periods after the first. -/
def periodicTailEnergy (L : ℕ) (R : ℕ → ℝ) : ℝ :=
  ∑ a : Fin L, residuePowerWeight 0 L ((a.val : ℝ) + 1 + L) * R (a.val + 1)^2

theorem periodicTailEnergy_nonneg (L : ℕ) (hL : 0 < L) (R : ℕ → ℝ) :
    0 ≤ periodicTailEnergy L R := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (residuePowerWeight_pos 0 (by exact_mod_cast hL)
    (by positivity)).le (sq_nonneg _)

/-- The complete Q energy is its literal first-period mass plus the exact
positive contribution of every later period. -/
theorem periodic_qEnergy_first_tail (L : ℕ) (hL : 0 < L)
    (R : ℕ → ℝ) {C : ℝ} (hR : ∀ n, |R n| ≤ C)
    (hp : ∀ n, R (n + L) = R n) :
    inversePowerMean 0 (fun n => R n^2) =
      crtReciprocalEnergy L R / zetaTwo + periodicTailEnergy L R := by
  have hC : 0 ≤ C := (abs_nonneg (R 0)).trans (hR 0)
  have hsq : ∀ n, |R n^2| ≤ C^2 := by
    intro n
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_le.mp (hR n)]
  rw [periodic_inversePowerMean 0 L hL _ hsq (by intro n; rw [hp])]
  unfold crtReciprocalEnergy periodicTailEnergy
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [residuePowerWeight_shift 0 (by exact_mod_cast hL) (by positivity)]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Uniform two-sided arithmetic control of the complete periodic tail. -/
theorem periodicTailEnergy_bounds (L : ℕ) (hL : 0 < L) (R : ℕ → ℝ) :
    (1 - 1 / zetaTwo) * periodSquareEnergy L R / (L : ℝ)^2 ≤
      periodicTailEnergy L R ∧
    periodicTailEnergy L R ≤ periodSquareEnergy L R / (L : ℝ)^2 := by
  unfold periodSquareEnergy periodicTailEnergy
  rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div]
  constructor
  · apply Finset.sum_le_sum
    intro a _
    have h := (residueSquareWeight_tail_bounds L hL
      (by positivity : (0 : ℝ) < (a.val : ℝ) + 1)
      (by exact_mod_cast (show a.val + 1 ≤ L from a.isLt))).1
    convert mul_le_mul_of_nonneg_right h (sq_nonneg (R (a.val + 1))) using 1; ring
  · apply Finset.sum_le_sum
    intro a _
    have h := (residueSquareWeight_tail_bounds L hL
      (by positivity : (0 : ℝ) < (a.val : ℝ) + 1)
      (by exact_mod_cast (show a.val + 1 ≤ L from a.isLt))).2
    convert mul_le_mul_of_nonneg_right h (sq_nonneg (R (a.val + 1))) using 1; ring

/-- The lower tail comparison constant is strictly positive, directly from
the second and later atoms of the probability law. -/
theorem one_sub_inv_zetaTwo_pos : 0 < 1 - 1 / zetaTwo := by
  have h := residuePowerWeight_shift 0 (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1)
  have hp := residuePowerWeight_pos 0 (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 2)
  have hz := QResidueConditional.residuePowerWeight_zeroClass 1
  norm_num at h hz
  rw [one_div]
  linarith

/-- Vanishing of the entire tail is equivalent to a purely finite
unweighted period-energy criterion, even while the periods vary. -/
theorem periodicTailEnergy_tendsto_zero_iff (L : ℕ → ℕ) (R : ℕ → ℕ → ℝ)
    (hL : ∀ j, 0 < L j) :
    Filter.Tendsto (fun j => periodicTailEnergy (L j) (R j))
        Filter.atTop (nhds 0) ↔
      Filter.Tendsto (fun j => periodSquareEnergy (L j) (R j) / (L j : ℝ)^2)
        Filter.atTop (nhds 0) := by
  have hc := one_sub_inv_zetaTwo_pos
  have hn (j) : 0 ≤ periodSquareEnergy (L j) (R j) / (L j : ℝ)^2 := by
    apply div_nonneg _ (sq_nonneg _)
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  constructor
  · intro h
    have ht := h.div_const (1 - 1 / zetaTwo)
    simp only [zero_div] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht hn
    intro j
    apply (le_div_iff₀ hc).mpr
    calc
      periodSquareEnergy (L j) (R j) / (L j : ℝ)^2 * (1 - 1 / zetaTwo) =
          (1 - 1 / zetaTwo) * periodSquareEnergy (L j) (R j) / (L j : ℝ)^2 := by ring
      _ ≤ periodicTailEnergy (L j) (R j) :=
        (periodicTailEnergy_bounds (L j) (hL j) (R j)).1
  · intro h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun j => periodicTailEnergy_nonneg (L j) (hL j) (R j))
      (fun j => (periodicTailEnergy_bounds (L j) (hL j) (R j)).2)

/-- The same identity holds for the actual Q-Hilbert approximation error. -/
theorem periodic_qError_first_tail (L : ℕ) (hL : 0 < L)
    (f : QHilbert) {C : ℝ} (hf : ∀ n, |qSequence f n| ≤ C)
    (hp : ∀ n, qSequence f (n + L) = qSequence f n) :
    ‖qOne - f‖^2 = crtReciprocalEnergy L (fun n => 1 - qSequence f n) / zetaTwo +
      periodicTailEnergy L (fun n => 1 - qSequence f n) := by
  rw [qError_eq_inversePowerMean]
  apply periodic_qEnergy_first_tail L hL
  · intro n
    calc
      |1 - qSequence f n| ≤ 1 + |qSequence f n| := by
        simpa [sub_eq_add_neg] using abs_add_le (1 : ℝ) (-qSequence f n)
      _ ≤ 1 + C := add_le_add le_rfl (hf n)
  · intro n
    rw [hp]

end RiemannResearch.RH.ZetaTwoProbability
