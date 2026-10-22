/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Exact reciprocal overlap partitions

Source: the finite partition argument developed in the review of
Michel Balazard, arXiv:1812.04309, Propositions 6--7 (19 October 2026).
The paper motivates the dual-system application; the row and column
identities here are elementary finite telescopes. No novelty is claimed.
The concrete RH consumer is MobiusTriangularEnergy.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis

/-- The length of `[j,j+1] ∩ (-∞,t]`. -/
def unitRamp (j : ℕ) (t : ℝ) : ℝ :=
  max (t - (j : ℝ)) 0 - max (t - ((j + 1 : ℕ) : ℝ)) 0

theorem unitRamp_monotone (j : ℕ) : Monotone (unitRamp j) := by
  intro a b hab
  simp only [unitRamp, Nat.cast_add, Nat.cast_one, max_def]
  split_ifs <;> linarith

theorem unitRamp_eq_zero_of_le (j : ℕ) (t : ℝ) (ht : t ≤ (j : ℝ)) :
    unitRamp j t = 0 := by
  have ht' : t ≤ ((j + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  rw [unitRamp, max_eq_right (sub_nonpos.mpr ht),
    max_eq_right (sub_nonpos.mpr ht')]
  ring

theorem unitRamp_eq_one_of_ge (j : ℕ) (t : ℝ)
    (ht : ((j + 1 : ℕ) : ℝ) ≤ t) :
    unitRamp j t = 1 := by
  have ht' : (j : ℝ) ≤ t := by
    have hj : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by norm_num
    exact hj.trans ht
  rw [unitRamp, max_eq_left (sub_nonneg.mpr ht'),
    max_eq_left (sub_nonneg.mpr ht)]
  push_cast
  ring

private theorem sum_range_sub_shift_real (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (f j - f (j + 1))) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem sum_unitRamp_shift (n : ℕ) (t : ℝ) :
    (∑ j : Fin n, unitRamp (j.val + 1) t) =
      max (t - 1) 0 - max (t - ((n + 1 : ℕ) : ℝ)) 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => unitRamp (j + 1) t) n]
  simpa [unitRamp, Nat.add_assoc] using
    sum_range_sub_shift_real (fun j => max (t - ((j + 1 : ℕ) : ℝ)) 0) n

theorem sum_unitRamp_shift_of_bounds (n : ℕ) (t : ℝ)
    (ht1 : 1 ≤ t) (htN : t ≤ ((n + 1 : ℕ) : ℝ)) :
    (∑ j : Fin n, unitRamp (j.val + 1) t) = t - 1 := by
  rw [sum_unitRamp_shift, max_eq_left (sub_nonneg.mpr ht1),
    max_eq_right (sub_nonpos.mpr htN), sub_zero]

/-- Overlap kernel for a decreasing partition of `[1,n+1]`. -/
def decreasingRampKernel (n : ℕ) (x : ℕ → ℝ) (i j : Fin n) : ℝ :=
  (unitRamp (j.val + 1) (x i.val) -
    unitRamp (j.val + 1) (x (i.val + 1))) / ((n + 1 : ℕ) : ℝ)

theorem decreasingRampKernel_nonneg (n : ℕ) (x : ℕ → ℝ)
    (hdec : ∀ i < n, x (i + 1) ≤ x i) (i j : Fin n) :
    0 ≤ decreasingRampKernel n x i j := by
  unfold decreasingRampKernel
  apply div_nonneg
  · exact sub_nonneg.mpr (unitRamp_monotone _ (hdec i.val i.isLt))
  · positivity

theorem decreasingRampKernel_row (n : ℕ) (x : ℕ → ℝ)
    (hb : ∀ i ≤ n, 1 ≤ x i ∧ x i ≤ ((n + 1 : ℕ) : ℝ)) (i : Fin n) :
    (∑ j : Fin n, decreasingRampKernel n x i j) =
      (x i.val - x (i.val + 1)) / ((n + 1 : ℕ) : ℝ) := by
  unfold decreasingRampKernel
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    sum_unitRamp_shift_of_bounds n (x i.val) (hb _ (by omega)).1 (hb _ (by omega)).2,
    sum_unitRamp_shift_of_bounds n (x (i.val + 1)) (hb _ (by omega)).1
      (hb _ (by omega)).2]
  ring

theorem decreasingRampKernel_col (n : ℕ) (x : ℕ → ℝ)
    (hfirst : x 0 = ((n + 1 : ℕ) : ℝ)) (hlast : x n = 1) (j : Fin n) :
    (∑ i : Fin n, decreasingRampKernel n x i j) =
      1 / ((n + 1 : ℕ) : ℝ) := by
  unfold decreasingRampKernel
  rw [← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    unitRamp (j.val + 1) (x i) - unitRamp (j.val + 1) (x (i + 1))) n]
  rw [sum_range_sub_shift_real, hfirst, hlast]
  have hupper : ((j.val + 1 + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show j.val + 1 + 1 ≤ n + 1 by omega)
  have hlower : (1 : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ j.val + 1 by omega)
  rw [unitRamp_eq_one_of_ge _ _ hupper, unitRamp_eq_zero_of_le _ _ hlower]
  ring

/-- Reciprocal partition endpoints; physical coordinate `k=i+1`. -/
def reciprocalCut (n i : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ)

theorem reciprocalCut_bounds (n i : ℕ) (hi : i ≤ n) :
    1 ≤ reciprocalCut n i ∧ reciprocalCut n i ≤ ((n + 1 : ℕ) : ℝ) := by
  have hden : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
  have hden1 : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ i + 1 by omega)
  have hdenN : ((i + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_le_add_right hi 1)
  unfold reciprocalCut
  constructor
  · apply (le_div_iff₀ hden).mpr
    simpa using hdenN
  · apply (div_le_iff₀ hden).mpr
    have hN : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    nlinarith

theorem reciprocalCut_decreasing (n i : ℕ) :
    reciprocalCut n (i + 1) ≤ reciprocalCut n i := by
  unfold reciprocalCut
  apply div_le_div_of_nonneg_left
  · positivity
  · positivity
  · push_cast
    linarith

theorem reciprocalCut_first (n : ℕ) :
    reciprocalCut n 0 = ((n + 1 : ℕ) : ℝ) := by simp [reciprocalCut]

theorem reciprocalCut_last (n : ℕ) : reciprocalCut n n = 1 := by
  unfold reciprocalCut
  exact div_self (by positivity)

def reciprocalOverlap (n : ℕ) (i j : Fin n) : ℝ :=
  decreasingRampKernel n (reciprocalCut n) i j

theorem reciprocalOverlap_nonneg (n : ℕ) (i j : Fin n) :
    0 ≤ reciprocalOverlap n i j :=
  decreasingRampKernel_nonneg n _ (fun i _ => reciprocalCut_decreasing n i) i j

theorem reciprocalOverlap_row (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, reciprocalOverlap n i j) =
      1 / (((i.val + 1 : ℕ) : ℝ) * ((i.val + 2 : ℕ) : ℝ)) := by
  unfold reciprocalOverlap
  rw [decreasingRampKernel_row n _ (fun i hi => reciprocalCut_bounds n i hi)]
  unfold reciprocalCut
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hi : (((i.val + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hi' : (((i.val + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  simp only [Nat.add_assoc]
  push_cast at *
  field_simp [hn, hi, hi']; ring

theorem reciprocalOverlap_col (n : ℕ) (j : Fin n) :
    (∑ i : Fin n, reciprocalOverlap n i j) =
      1 / ((n + 1 : ℕ) : ℝ) :=
  decreasingRampKernel_col n _ (reciprocalCut_first n) (reciprocalCut_last n) j

end RiemannResearch.Analysis
