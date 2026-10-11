/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Ring

/-!
# Finite stop-loss identities for ordinate-gap statistics

These are the finite algebraic part of the empty-interval/gap-distribution
method in Jens Marklof, *Distribution modulo one and Ratner's theorem*,
Section 2.1 (pp. 220–222), in Equidistribution in Number Theory,
Springer, 2007. This source supplies the gap/empty-interval interpretation.

For circular gaps of total length one, the normalized empty-interval
probability is a mean of `max (gap - L) 0`.  This file proves the exact
stop-loss identities, tail estimates, and centered marked identities.
It does not identify a finite sum with a geometric interval measure or
assert any equidistribution or zeta-gap theorem.
-/

noncomputable section

open scoped BigOperators
open Filter

namespace RiemannResearch.ZeroOrdinateStopLoss

variable {ι : Type*}

def stopLossSum (s : Finset ι) (g : ι → ℝ) (L : ℝ) : ℝ :=
  ∑ i ∈ s, max (g i - L) 0

def meanGap (s : Finset ι) (g : ι → ℝ) : ℝ :=
  (∑ i ∈ s, g i) / (s.card : ℝ)

def meanStopLoss (s : Finset ι) (g : ι → ℝ) (L : ℝ) : ℝ :=
  stopLossSum s g L / (s.card : ℝ)

def markedMeanGap (s : Finset ι) (g w : ι → ℝ) : ℝ :=
  (∑ i ∈ s, w i * g i) / (s.card : ℝ)

def markedStopLoss (s : Finset ι) (g w : ι → ℝ) (L : ℝ) : ℝ :=
  (∑ i ∈ s, w i * max (g i - L) 0) / (s.card : ℝ)

def centeredMarkedStopLoss (s : Finset ι) (g w : ι → ℝ) (c L : ℝ) : ℝ :=
  markedStopLoss s g w L - c * meanStopLoss s g L

theorem excess_eq_sub_min (a L : ℝ) : max (a - L) 0 = a - min a L := by
  by_cases h : a ≤ L
  · simp [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
  · have h' : L ≤ a := le_of_lt (lt_of_not_ge h)
    simp [min_eq_right h', max_eq_left (sub_nonneg.mpr h')]

theorem stopLossSum_eq_sum_sub_min (s : Finset ι) (g : ι → ℝ) (L : ℝ) :
    stopLossSum s g L = (∑ i ∈ s, g i) - ∑ i ∈ s, min (g i) L := by
  simp only [stopLossSum, excess_eq_sub_min, Finset.sum_sub_distrib]

theorem meanStopLoss_eq_meanGap_sub_min
    (s : Finset ι) (g : ι → ℝ) (L : ℝ) :
    meanStopLoss s g L = meanGap s g -
      (∑ i ∈ s, min (g i) L) / (s.card : ℝ) := by
  simp only [meanStopLoss, meanGap, stopLossSum_eq_sum_sub_min, sub_div]

/-- The finite mean-one void identity, including the bounded truncation term. -/
theorem meanStopLoss_eq_one_sub_min
    (s : Finset ι) (g : ι → ℝ) (L : ℝ) (hmean : meanGap s g = 1) :
    meanStopLoss s g L = 1 -
      (∑ i ∈ s, min (g i) L) / (s.card : ℝ) := by
  rw [meanStopLoss_eq_meanGap_sub_min, hmean]

theorem markedStopLoss_eq_markedMeanGap_sub_min
    (s : Finset ι) (g w : ι → ℝ) (L : ℝ) :
    markedStopLoss s g w L = markedMeanGap s g w -
      (∑ i ∈ s, w i * min (g i) L) / (s.card : ℝ) := by
  simp only [markedStopLoss, markedMeanGap, excess_eq_sub_min,
    mul_sub, Finset.sum_sub_distrib, sub_div]

theorem stopLossSum_nonneg (s : Finset ι) (g : ι → ℝ) (L : ℝ) :
    0 ≤ stopLossSum s g L :=
  Finset.sum_nonneg fun i _ => le_max_right (g i - L) 0

theorem meanStopLoss_nonneg (s : Finset ι) (g : ι → ℝ) (L : ℝ) :
    0 ≤ meanStopLoss s g L :=
  div_nonneg (stopLossSum_nonneg s g L) (Nat.cast_nonneg _)

theorem stopLossSum_antitone (s : Finset ι) (g : ι → ℝ) :
    Antitone (stopLossSum s g) := by
  intro L K hLK
  exact Finset.sum_le_sum fun i _ => max_le_max_right 0 (sub_le_sub_left hLK (g i))

theorem meanStopLoss_antitone (s : Finset ι) (g : ι → ℝ) :
    Antitone (meanStopLoss s g) := by
  intro L K hLK
  exact div_le_div_of_nonneg_right
    (stopLossSum_antitone s g hLK) (Nat.cast_nonneg _)

theorem stopLossSum_zero (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) : stopLossSum s g 0 = ∑ i ∈ s, g i := by
  apply Finset.sum_congr rfl
  intro i hi
  simp only [sub_zero, max_eq_left (hg i hi)]

theorem meanStopLoss_zero (s : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) : meanStopLoss s g 0 = meanGap s g := by
  simp only [meanStopLoss, meanGap, stopLossSum_zero s g hg]

theorem markedStopLoss_zero (s : Finset ι) (g w : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) : markedStopLoss s g w 0 = markedMeanGap s g w := by
  unfold markedStopLoss markedMeanGap
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [sub_zero, max_eq_left (hg i hi)]

/-- A tail count is bounded by the stop-loss transform at any lower threshold. -/
theorem tail_card_mul_le_stopLossSum
    (s : Finset ι) (g : ι → ℝ) (a b : ℝ) :
    (b - a) * ((s.filter fun i => b ≤ g i).card : ℝ) ≤ stopLossSum s g a := by
  classical
  calc
    (b - a) * ((s.filter fun i => b ≤ g i).card : ℝ) =
        ∑ i ∈ s.filter (fun i => b ≤ g i), (b - a) := by simp [mul_comm]; ring
    _ ≤ ∑ i ∈ s.filter (fun i => b ≤ g i), max (g i - a) 0 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (sub_le_sub_right (Finset.mem_filter.mp hi).2 a).trans (le_max_left _ _)
    _ ≤ stopLossSum s g a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i _ _
      exact le_max_right _ _

theorem tail_card_le_stopLossSum_div
    (s : Finset ι) (g : ι → ℝ) {a b : ℝ} (hab : a < b) :
    ((s.filter fun i => b ≤ g i).card : ℝ) ≤ stopLossSum s g a / (b - a) := by
  classical
  apply (le_div_iff₀ (sub_pos.mpr hab)).2
  simpa only [mul_comm] using tail_card_mul_le_stopLossSum s g a b

theorem tail_frequency_le_meanStopLoss_div
    (s : Finset ι) (g : ι → ℝ) {a b : ℝ} (hab : a < b) :
    ((s.filter fun i => b ≤ g i).card : ℝ) / (s.card : ℝ) ≤
      meanStopLoss s g a / (b - a) := by
  classical
  calc
    ((s.filter fun i => b ≤ g i).card : ℝ) / (s.card : ℝ) ≤
        (stopLossSum s g a / (b - a)) / (s.card : ℝ) :=
      div_le_div_of_nonneg_right (tail_card_le_stopLossSum_div s g hab) (Nat.cast_nonneg _)
    _ = meanStopLoss s g a / (b - a) := by
      simp only [meanStopLoss, div_div]
      rw [mul_comm]

/-- Exact centering: the factorization defect is a marked stop-loss sum. -/
theorem centeredMarkedStopLoss_eq_sum
    (s : Finset ι) (g w : ι → ℝ) (c L : ℝ) :
    centeredMarkedStopLoss s g w c L =
      (∑ i ∈ s, (w i - c) * max (g i - L) 0) / (s.card : ℝ) := by
  have hsum : (∑ i ∈ s, (w i - c) * max (g i - L) 0) =
      (∑ i ∈ s, w i * max (g i - L) 0) - c * stopLossSum s g L := by
    simp only [sub_mul, Finset.sum_sub_distrib, stopLossSum, Finset.mul_sum]
  rw [hsum]
  unfold centeredMarkedStopLoss markedStopLoss meanStopLoss
  ring

theorem abs_centeredMarkedStopLoss_le
    (s : Finset ι) (g w : ι → ℝ) (c L C : ℝ)
    (hw : ∀ i ∈ s, |w i - c| ≤ C) :
    |centeredMarkedStopLoss s g w c L| ≤ C * meanStopLoss s g L := by
  rw [centeredMarkedStopLoss_eq_sum, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (s.card : ℝ) from Nat.cast_nonneg _)]
  have hsum : |∑ i ∈ s, (w i - c) * max (g i - L) 0| ≤ C * stopLossSum s g L := by
    calc
      |∑ i ∈ s, (w i - c) * max (g i - L) 0| ≤
          ∑ i ∈ s, |(w i - c) * max (g i - L) 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ s, |w i - c| * max (g i - L) 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ max (g i - L) 0 from le_max_right _ _)]
      _ ≤ ∑ i ∈ s, C * max (g i - L) 0 := by
        exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hw i hi) (le_max_right _ _)
      _ = C * stopLossSum s g L := by rw [stopLossSum, Finset.mul_sum]
  calc
    |∑ i ∈ s, (w i - c) * max (g i - L) 0| / (s.card : ℝ) ≤
        (C * stopLossSum s g L) / (s.card : ℝ) :=
      div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
    _ = C * meanStopLoss s g L := by unfold meanStopLoss; ring

/-- The zero-threshold factorization defect is exactly a first-moment defect. -/
theorem centeredMarkedStopLoss_zero
    (s : Finset ι) (g w : ι → ℝ) (c : ℝ) (hg : ∀ i ∈ s, 0 ≤ g i) :
    centeredMarkedStopLoss s g w c 0 = markedMeanGap s g w - c * meanGap s g := by
  rw [centeredMarkedStopLoss, markedStopLoss_zero s g w hg, meanStopLoss_zero s g hg]

/-- If ordinary and gap-weighted first moments have the expected limits,
the centered zero-threshold marked stop-loss tends to zero. -/
theorem centeredMarkedStopLoss_zero_tendsto
    (s : ℕ → Finset ι) (g w : ℕ → ι → ℝ) (c : ℝ)
    (hg : ∀ n i, i ∈ s n → 0 ≤ g n i)
    (hmean : Tendsto (fun n => meanGap (s n) (g n)) atTop (nhds 1))
    (hmarked : Tendsto (fun n => markedMeanGap (s n) (g n) (w n)) atTop (nhds c)) :
    Tendsto (fun n => centeredMarkedStopLoss (s n) (g n) (w n) c 0) atTop (nhds 0) := by
  have heq : (fun n => centeredMarkedStopLoss (s n) (g n) (w n) c 0) =
      (fun n => markedMeanGap (s n) (g n) (w n) - c * meanGap (s n) (g n)) := by
    funext n
    exact centeredMarkedStopLoss_zero (s n) (g n) (w n) c (hg n)
  rw [heq]
  simpa only [mul_one, sub_self] using hmarked.sub (hmean.const_mul c)

end RiemannResearch.ZeroOrdinateStopLoss
