/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualConsecutiveOrdinates
import RiemannResearch.Analysis.ZeroOrdinateGapWindows

/-!
# Empty-window identities for actual consecutive ordinate cutoffs

The concrete ordinate enumeration is monotone, including repetitions. Its
consecutive open gap intervals are therefore pairwise disjoint. The finite
Lebesgue-measure and stop-loss identities apply without RH, simplicity, or
equidistribution assumptions.

The final ordinate is padded by `T`: the final gap is truncated at `T`.
The interval before the first listed zero is not included. Consequently the
exact total gap length is `T - cutoffOrdinate T 0`, retained in every formula.
This file identifies geometric gap-window starts. It does not claim a
circular wraparound identity or formalize an infinite zeta-gap limit law.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory Zeta23
open RiemannResearch.ZeroOrdinateStopLoss

namespace RiemannResearch.Analysis.ActualZeroOrdinate

theorem cutoffGapIntervals_pairwiseDisjoint (T : ℝ) :
    Set.PairwiseDisjoint (↑(Finset.range (Ncount 0 T)) : Set ℕ)
      (fun j => Ioo (cutoffOrdinate T j) (cutoffOrdinate T (j + 1))) := by
  intro i _ j _ hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hmid : cutoffOrdinate T (i + 1) ≤ cutoffOrdinate T j :=
      cutoffOrdinate_monotone T (Nat.succ_le_of_lt hij')
    exact (lt_irrefl x) (hxi.2.trans (hmid.trans_lt hxj.1))
  · have hmid : cutoffOrdinate T (j + 1) ≤ cutoffOrdinate T i :=
      cutoffOrdinate_monotone T (Nat.succ_le_of_lt hji')
    exact (lt_irrefl x) (hxj.2.trans (hmid.trans_lt hxi.1))

/-- Window starts inside the finite actual ordinate gaps, with the last gap
ending at the cutoff `T`. -/
def cutoffEmptyStarts (T L : ℝ) : Set ℝ :=
  ⋃ j ∈ Finset.range (Ncount 0 T),
    emptyStartsInGap (cutoffOrdinate T j) (cutoffOrdinate T (j + 1)) L

theorem volume_real_cutoffEmptyStarts (T : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    volume.real (cutoffEmptyStarts T L) =
      stopLossSum (Finset.range (Ncount 0 T)) (cutoffGap T) L := by
  unfold cutoffEmptyStarts cutoffGap
  exact volume_real_emptyStarts_eq_stopLossSum
      (Finset.range (Ncount 0 T)) (cutoffOrdinate T)
      (fun j => cutoffOrdinate T (j + 1)) hL
      (cutoffGapIntervals_pairwiseDisjoint T)

theorem cutoff_meanGap_exact (T : ℝ) :
    meanGap (Finset.range (Ncount 0 T)) (cutoffGap T) =
      (T - cutoffOrdinate T 0) / (Ncount 0 T : ℝ) := by
  simp only [meanGap, sum_cutoffGap, Finset.card_range]

/-- The truncation term remains an exact signed term. -/
theorem cutoff_meanStopLoss_exact (T L : ℝ) :
    meanStopLoss (Finset.range (Ncount 0 T)) (cutoffGap T) L =
      (T - cutoffOrdinate T 0) / (Ncount 0 T : ℝ) -
        (∑ j ∈ Finset.range (Ncount 0 T), min (cutoffGap T j) L) /
          (Ncount 0 T : ℝ) := by
  rw [meanStopLoss_eq_meanGap_sub_min, cutoff_meanGap_exact]
  simp only [Finset.card_range]

/-- Exact conversion between normalized-gap stop loss and physical
empty-window starting length. The chosen density `scale` is arbitrary. -/
theorem cutoff_scaled_meanStopLoss_eq_volume
    (T : ℝ) {scale L : ℝ} (hscale : 0 < scale) (hL : 0 ≤ L) :
    meanStopLoss (Finset.range (Ncount 0 T))
        (fun j => scale * cutoffGap T j) L =
      (scale / (Ncount 0 T : ℝ)) *
        volume.real (cutoffEmptyStarts T (L / scale)) := by
  simpa only [cutoffEmptyStarts, cutoffGap, Finset.card_range] using
    meanStopLoss_eq_scaled_emptyStarts_volume
      (Finset.range (Ncount 0 T)) (cutoffOrdinate T)
      (fun j => cutoffOrdinate T (j + 1)) hscale hL
      (cutoffGapIntervals_pairwiseDisjoint T)

/-- The endpoint contribution is visibly a truncated gap, not the interval
to an asserted next zero beyond `T`. -/
theorem cutoff_lastGap_emptyStarts (T L : ℝ) (n : ℕ)
    (hn : Ncount 0 T = n + 1) :
    emptyStartsInGap (cutoffOrdinate T n) (cutoffOrdinate T (n + 1)) L =
      Ioo (cutoffOrdinate T n) (T - L) := by
  rw [cutoffOrdinate_of_count_le hn.le, emptyStartsInGap_eq_Ioo]

end RiemannResearch.Analysis.ActualZeroOrdinate
