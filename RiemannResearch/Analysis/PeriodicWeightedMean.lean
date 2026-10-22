/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
Exact periodic discrepancy and Abel remainder estimates for the Q-DPP
arithmetic mean argument. Source: the elementary finite summation argument
in RH/QDPPGrowingWindowsResearch20261014.md.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.PeriodicWeightedMean

def partialSum (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, f i

lemma prefix_zero (f : ℕ → ℝ) : partialSum f 0 = 0 := by
  simp [partialSum]

lemma prefix_succ (f : ℕ → ℝ) (n : ℕ) :
    partialSum f (n + 1) = partialSum f n + f n := by
  simp only [partialSum, Finset.sum_range_succ]

/-- Abel summation with a boundary at w n; this version includes n=0. -/
theorem abel_identity (f w : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f i * w i) =
      partialSum f n * w n +
        ∑ i ∈ Finset.range n, partialSum f (i + 1) * (w i - w (i + 1)) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Finset.sum_range_succ, prefix_succ]
      ring

lemma telescoping_weights (w : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (w i - w (i + 1))) = w 0 - w n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

lemma abs_range_sum_le (u : ℕ → ℝ) (n : ℕ) :
    |∑ i ∈ Finset.range n, u i| ≤ ∑ i ∈ Finset.range n, |u i| := by
  exact Finset.abs_sum_le_sum_abs _ _

/-- The exact partialSum hypothesis produces the sharp B*w(0) bound. -/
theorem abel_bound (f w : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (hprefix : ∀ k ≤ n, |partialSum f k| ≤ B)
    (hwn : 0 ≤ w n)
    (hdec : ∀ i < n, w (i + 1) ≤ w i) :
    |∑ i ∈ Finset.range n, f i * w i| ≤ B * w 0 := by
  have hlast : |partialSum f n * w n| ≤ B * w n := by
    rw [abs_mul, abs_of_nonneg hwn]
    exact mul_le_mul_of_nonneg_right (hprefix n le_rfl) hwn
  have hterms :
      (∑ i ∈ Finset.range n,
        |partialSum f (i + 1) * (w i - w (i + 1))|) ≤
      ∑ i ∈ Finset.range n, B * (w i - w (i + 1)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hd : 0 ≤ w i - w (i + 1) := sub_nonneg.mpr (hdec i hin)
    rw [abs_mul, abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_right
      (hprefix (i + 1) (Nat.succ_le_of_lt hin)) hd
  calc
    |∑ i ∈ Finset.range n, f i * w i|
        = |partialSum f n * w n +
            ∑ i ∈ Finset.range n,
              partialSum f (i + 1) * (w i - w (i + 1))| := by
                rw [abel_identity]
    _ ≤ |partialSum f n * w n| +
          |∑ i ∈ Finset.range n,
            partialSum f (i + 1) * (w i - w (i + 1))| := abs_add_le _ _
    _ ≤ B * w n +
          ∑ i ∈ Finset.range n, B * (w i - w (i + 1)) := by
            exact add_le_add hlast
              ((abs_range_sum_le
                (fun i => partialSum f (i + 1) * (w i - w (i + 1))) n).trans hterms)
    _ = B * w 0 := by
      rw [← Finset.mul_sum, telescoping_weights]
      ring

def signedRemainder (f w : ℕ → ℝ) (a : ℝ) (n : ℕ) : ℝ :=
  partialSum (fun i => f i - a) n * w n +
    ∑ i ∈ Finset.range n,
      partialSum (fun j => f j - a) (i + 1) * (w i - w (i + 1))

/-- Exact arithmetic mean plus an explicit signed Abel remainder. -/
theorem weighted_mean_identity (f w : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f i * w i) =
      a * (∑ i ∈ Finset.range n, w i) + signedRemainder f w a n := by
  unfold signedRemainder
  rw [← abel_identity, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem signedRemainder_bound (f w : ℕ → ℝ) (a B : ℝ) (n : ℕ)
    (hprefix : ∀ k ≤ n, |partialSum (fun i => f i - a) k| ≤ B)
    (hwn : 0 ≤ w n)
    (hdec : ∀ i < n, w (i + 1) ≤ w i) :
    |signedRemainder f w a n| ≤ B * w 0 := by
  unfold signedRemainder
  rw [← abel_identity]
  exact abel_bound (fun i => f i - a) w n B hprefix hwn hdec

/-- Reduce every zero-mean periodic partialSum to a shorter one, without modulo
    machinery. The proof repeatedly removes a complete period. -/
theorem periodic_prefix_bound (g : ℕ → ℝ) (r : ℕ) (B : ℝ)
    (hr : 0 < r)
    (hper : ∀ i, g (i + r) = g i)
    (hblock : partialSum g r = 0)
    (hshort : ∀ k < r, |partialSum g k| ≤ B) :
    ∀ n, |partialSum g n| ≤ B := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnr : n < r
      · exact hshort n hnr
      · have hrn : r ≤ n := Nat.le_of_not_gt hnr
        have hnpos : 0 < n := lt_of_lt_of_le hr hrn
        have hlt : n - r < n := Nat.sub_lt hnpos hr
        have hsplit : partialSum g n = partialSum g (n - r) := by
          have hn : r + (n - r) = n := Nat.add_sub_of_le hrn
          conv_lhs => rw [← hn]
          unfold partialSum
          rw [Finset.sum_range_add]
          have hz : (∑ i ∈ Finset.range r, g i) = 0 := hblock
          rw [hz, zero_add]
          apply Finset.sum_congr rfl
          intro i hi
          simpa only [Nat.add_comm] using hper i
        rw [hsplit]
        exact ih (n - r) hlt

/-- A nonnegative periodic sequence has partialSum discrepancy at most one full
    period's mass. This is the only input needed for the weighted mean error. -/
theorem nonnegative_periodic_discrepancy (f : ℕ → ℝ) (r : ℕ) (a : ℝ)
    (hr : 0 < r)
    (ha : 0 ≤ a)
    (hpos : ∀ i, 0 ≤ f i)
    (hper : ∀ i, f (i + r) = f i)
    (hblock : partialSum f r = (r : ℝ) * a) :
    ∀ n, |partialSum (fun i => f i - a) n| ≤ (r : ℝ) * a := by
  have hcenter (k : ℕ) :
      partialSum (fun i => f i - a) k = partialSum f k - (k : ℝ) * a := by
    simp only [partialSum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  apply periodic_prefix_bound (fun i => f i - a) r ((r : ℝ) * a) hr
  · intro i
    rw [hper i]
  · rw [hcenter, hblock, sub_self]
  · intro k hk
    have hs0 : 0 ≤ partialSum f k := by
      exact Finset.sum_nonneg (by intro i hi; exact hpos i)
    have hsle : partialSum f k ≤ partialSum f r := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.le_of_lt hk))
        (by intro i hi hnot; exact hpos i)
    have hkcast : (k : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.le_of_lt hk
    have hka : (k : ℝ) * a ≤ (r : ℝ) * a :=
      mul_le_mul_of_nonneg_right hkcast ha
    have hka0 : 0 ≤ (k : ℝ) * a := mul_nonneg (Nat.cast_nonneg k) ha
    rw [hcenter]
    apply abs_le.mpr
    constructor <;> linarith

end RiemannResearch.Analysis.PeriodicWeightedMean
