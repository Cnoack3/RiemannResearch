/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ZeroOrdinateStopLoss
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Exact finite gap-window geometry

For a gap `(a,b)` and a nonnegative window length `L`, the start points of
windows that stay strictly inside that gap form `(a,b-L)`.  Their Lebesgue
measure is `max ((b-a)-L) 0`.  A finite disjoint family of gaps therefore
has empty-window starting length equal to its stop-loss sum.

This is the finite geometric mechanism in Section 2.1 of the supplied
Jens Marklof chapter, *Distribution modulo one and Ratner's theorem*,
pp. 220--222.  Strict endpoints are used; the finite omitted endpoints
have zero Lebesgue measure.  Circular wraparound and the identification
of these gaps with zeta ordinates are separate constructions.
-/

open scoped BigOperators
open Set MeasureTheory

noncomputable section

namespace RiemannResearch.ZeroOrdinateStopLoss

variable {ι : Type*}

def emptyStartsInGap (a b L : ℝ) : Set ℝ := {x | a < x ∧ x + L < b}

theorem emptyStartsInGap_eq_Ioo (a b L : ℝ) :
    emptyStartsInGap a b L = Ioo a (b - L) := by
  ext x
  simp only [emptyStartsInGap, mem_setOf_eq, mem_Ioo, lt_sub_iff_add_lt]

theorem emptyStartsInGap_subset_gap (a b : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    emptyStartsInGap a b L ⊆ Ioo a b := by
  intro x hx
  exact ⟨hx.1, (le_add_of_nonneg_right hL).trans_lt hx.2⟩

theorem volume_real_emptyStartsInGap (a b L : ℝ) :
    volume.real (emptyStartsInGap a b L) = max ((b - a) - L) 0 := by
  rw [emptyStartsInGap_eq_Ioo, Real.volume_real_Ioo]
  congr 1
  ring

/-- Exact total starting length for a finite disjoint collection of gaps. -/
theorem volume_real_emptyStarts_eq_stopLossSum
    (s : Finset ι) (a b : ι → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hd : Set.PairwiseDisjoint (↑s : Set ι) (fun i => Ioo (a i) (b i))) :
    volume.real (⋃ i ∈ s, emptyStartsInGap (a i) (b i) L) =
      stopLossSum s (fun i => b i - a i) L := by
  have hd' : Set.PairwiseDisjoint (↑s : Set ι)
      (fun i => emptyStartsInGap (a i) (b i) L) := by
    intro i hi j hj hij
    exact (hd hi hj hij).mono
      (emptyStartsInGap_subset_gap (a i) (b i) hL)
      (emptyStartsInGap_subset_gap (a j) (b j) hL)
  have hm : ∀ i ∈ s, MeasurableSet (emptyStartsInGap (a i) (b i) L) := by
    intro i _
    rw [emptyStartsInGap_eq_Ioo]
    exact measurableSet_Ioo
  have hf : ∀ i ∈ s, volume (emptyStartsInGap (a i) (b i) L) ≠ ⊤ := by
    intro i _
    rw [emptyStartsInGap_eq_Ioo, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  rw [measureReal_biUnion_finset hd' hm hf]
  simp only [volume_real_emptyStartsInGap, stopLossSum]

theorem stopLossSum_scale (s : Finset ι) (g : ι → ℝ) {scale : ℝ}
    (hscale : 0 < scale) (L : ℝ) :
    stopLossSum s (fun i => scale * g i) L =
      scale * stopLossSum s g (L / scale) := by
  unfold stopLossSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_max_of_nonneg _ _ hscale.le, mul_zero, mul_sub,
    mul_div_cancel₀ L (ne_of_gt hscale)]

/-- Scaling physical gaps to unit-density gaps gives the normalized
empty-window identity, with all scaling factors retained. -/
theorem meanStopLoss_eq_scaled_emptyStarts_volume
    (s : Finset ι) (a b : ι → ℝ) {scale L : ℝ}
    (hscale : 0 < scale) (hL : 0 ≤ L)
    (hd : Set.PairwiseDisjoint (↑s : Set ι) (fun i => Ioo (a i) (b i))) :
    meanStopLoss s (fun i => scale * (b i - a i)) L =
      (scale / (s.card : ℝ)) *
        volume.real (⋃ i ∈ s, emptyStartsInGap (a i) (b i) (L / scale)) := by
  rw [volume_real_emptyStarts_eq_stopLossSum s a b (div_nonneg hL hscale.le) hd]
  unfold meanStopLoss
  rw [stopLossSum_scale s (fun i => b i - a i) hscale L]
  ring

end RiemannResearch.ZeroOrdinateStopLoss
