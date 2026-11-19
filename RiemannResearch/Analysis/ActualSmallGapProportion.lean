/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualConsecutiveOrdinates
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The normalized proportion of small consecutive gaps

The ordinate list counts all copies at heights in `(0,T]`. Only pairs whose
two endpoints are present are counted. Thus the cutoff padding at the final
ordinate contributes zero terms to this statistic. The full counting
convention in Lamzouri's arXiv:2611.14486v1 adds at most one term.

The theorem below isolates the analytic separated-pair estimate from the
topological step that makes the proportion uniform at all large heights.
-/

noncomputable section

open Filter Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Internal adjacent gaps in the finite chronological list, with multiplicity. -/
def smallGapIndices (gapLimit T : ℝ) : Finset ℕ :=
  (Finset.range (Ncount 0 T - 1)).filter
    (fun j => cutoffGap T j * Real.log T ≤ 2 * Real.pi * gapLimit)

/-- The marked occurrence indices are precisely the two endpoints of
every measured small internal gap. -/
def smallGapEndpoints (gapLimit T : ℝ) : Finset ℕ :=
  smallGapIndices gapLimit T ∪ (smallGapIndices gapLimit T).image Nat.succ

theorem smallGapEndpoints_card_le (gapLimit T : ℝ) :
    (smallGapEndpoints gapLimit T).card ≤ 2*(smallGapIndices gapLimit T).card := by
  calc
    _ ≤ (smallGapIndices gapLimit T).card + ((smallGapIndices gapLimit T).image Nat.succ).card :=
      Finset.card_union_le _ _
    _ ≤ _ := by
      have hi := Finset.card_image_le (s := smallGapIndices gapLimit T) (f := Nat.succ)
      omega

theorem smallGapEndpoints_subset (gapLimit T : ℝ) :
    smallGapEndpoints gapLimit T ⊆ Finset.range (Ncount 0 T) := by
  intro j hj
  rw [Finset.mem_range]
  rcases Finset.mem_union.mp hj with hleft | hright
  · have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hleft).1
    omega
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hright
    have hk' := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    omega

/-- Removing all marked endpoints leaves pairwise separation, even with
repeated ordinates in the original list. -/
theorem separation_of_unmarked_index {gapLimit T : ℝ} {i j : ℕ}
    (hlog : 0 ≤ Real.log T) (hij : i < j) (hj : j < Ncount 0 T)
    (hi : i ∉ smallGapEndpoints gapLimit T) :
    2 * Real.pi * gapLimit < (cutoffOrdinate T j - cutoffOrdinate T i) * Real.log T := by
  have him : i ∈ Finset.range (Ncount 0 T - 1) := Finset.mem_range.mpr (by omega)
  have hgap : 2 * Real.pi * gapLimit < cutoffGap T i * Real.log T := by
    by_contra! hle
    exact hi (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨him, hle⟩))
  apply hgap.trans_le
  exact mul_le_mul_of_nonneg_right
    (sub_le_sub_right (cutoffOrdinate_monotone T (Nat.succ_le_of_lt hij)) _) hlog

/-- Every internal adjacent ordinate collision is marked at both ends. -/
theorem endpoints_of_ordinate_collision {gapLimit T : ℝ} {i : ℕ}
    (hgapLimit : 0 ≤ gapLimit) (hi : i + 1 < Ncount 0 T)
    (hgap : cutoffOrdinate T (i + 1) = cutoffOrdinate T i) :
    i ∈ smallGapEndpoints gapLimit T ∧ i + 1 ∈ smallGapEndpoints gapLimit T := by
  have hmarked : i ∈ smallGapIndices gapLimit T := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    simp only [cutoffGap, hgap, sub_self, zero_mul]
    positivity
  exact ⟨Finset.mem_union_left _ hmarked,
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hmarked, rfl⟩)⟩

/-- Fraction normalized by the count of all zero occurrences up to height `T`. -/
def smallGapFraction (gapLimit T : ℝ) : ℝ :=
  ((smallGapIndices gapLimit T).card : ℝ) / (Ncount 0 T : ℝ)

/-- Lower asymptotic proportion of internal gaps on the global log-height scale. -/
def smallGapProportion (gapLimit : ℝ) : ℝ :=
  Filter.liminf (smallGapFraction gapLimit) atTop

theorem smallGapFraction_nonneg (gapLimit T : ℝ) : 0 ≤ smallGapFraction gapLimit T := by
  unfold smallGapFraction
  positivity

theorem smallGapFraction_le_one (gapLimit T : ℝ) : smallGapFraction gapLimit T ≤ 1 := by
  have hcard : (smallGapIndices gapLimit T).card ≤ Ncount 0 T :=
    calc
      (smallGapIndices gapLimit T).card ≤ (Finset.range (Ncount 0 T - 1)).card :=
        Finset.card_filter_le _ _
      _ ≤ Ncount 0 T := by simp
  by_cases hN : Ncount 0 T = 0
  · simp [smallGapFraction, hN]
  · have hN' : (0 : ℝ) < (Ncount 0 T : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    apply (div_le_one hN').2
    exact_mod_cast hcard

theorem smallGapFraction_mono {gapLimit κ : ℝ} (h : gapLimit ≤ κ) (T : ℝ) :
    smallGapFraction gapLimit T ≤ smallGapFraction κ T := by
  have hi : smallGapIndices gapLimit T ⊆ smallGapIndices κ T := by
    intro j hj
    obtain ⟨hm, hg⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hm,
      hg.trans (mul_le_mul_of_nonneg_left h (by positivity))⟩
  unfold smallGapFraction
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hi) (by positivity)

theorem smallGapProportion_monotone : Monotone smallGapProportion := by
  intro gapLimit κ h
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall (smallGapFraction_mono h))
    ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall (smallGapFraction_nonneg gapLimit))⟩
    (Filter.isCoboundedUnder_ge_of_le (atTop : Filter ℝ) (smallGapFraction_le_one κ))

/-- Once two endpoints from each small gap have been removed, an analytic
estimate bounds the positive test mass by one plus a deletion loss and a
height error. The estimate is needed only when the small-gap fraction is
less than one quarter. -/
def separatedPairEstimate (gapLimit M : ℝ) : Prop :=
  ∃ loss error : ℝ → ℝ, ContinuousAt loss 0 ∧ loss 0 = 0 ∧
    Tendsto error atTop (𝓝 0) ∧
    ∀ᶠ T : ℝ in atTop, smallGapFraction gapLimit T < 1 / 4 →
      M ≤ 1 + loss (smallGapFraction gapLimit T) + error T

/-- Any strictly positive excess in the separated-pair test gives a positive
uniform lower proportion, with the real-valued cutoff and actual zero list. -/
theorem smallGapProportion_pos_of_separatedPairEstimate
    {gapLimit M : ℝ} (hM : 1 < M) (h : separatedPairEstimate gapLimit M) :
    0 < smallGapProportion gapLimit := by
  obtain ⟨loss, error, hloss, hz, herror, hpair⟩ := h
  have hε : 0 < (M - 1) / 3 := by linarith
  obtain ⟨r, hr, hc⟩ := Metric.continuousAt_iff.mp hloss ((M - 1) / 3) hε
  have he := Metric.tendsto_nhds.mp herror ((M - 1) / 3) hε
  have hf : ∀ᶠ T : ℝ in atTop, min (1 / 4 : ℝ) r ≤ smallGapFraction gapLimit T := by
    filter_upwards [hpair, he] with T ht hsmall
    by_contra! hfail
    have hfr := lt_of_lt_of_le hfail (min_le_right _ _)
    have hfq := lt_of_lt_of_le hfail (min_le_left _ _)
    have hd : dist (smallGapFraction gapLimit T) 0 < r := by
      simpa [Real.dist_eq, abs_of_nonneg (smallGapFraction_nonneg gapLimit T)] using hfr
    have hld := hc hd
    rw [hz, Real.dist_eq, sub_zero] at hld
    rw [Real.dist_eq, sub_zero] at hsmall
    have hl := (abs_lt.mp hld).2
    have herr := (abs_lt.mp hsmall).2
    have hab := ht hfq
    linarith
  have hco := Filter.isCoboundedUnder_ge_of_le (atTop : Filter ℝ)
    (smallGapFraction_le_one gapLimit)
  exact lt_of_lt_of_le (lt_min (by norm_num) hr) (Filter.le_liminf_of_le hco hf)

end RiemannResearch.Analysis.ActualZeroOrdinate
