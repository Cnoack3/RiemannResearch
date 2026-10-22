/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Exact truncation criteria for nonnegative series

The clipping identity separates a bounded energy series into a large-term
indicator and the complete small-term energy. A positive clipping level
preserves summability; no lower bound on the original series is asserted.

Terminology source: Dan Romik, *MATH/STAT 235A Probability Theory*, Fall 2013,
Theorem 10.6 and Example 10.7:
https://www.math.ucdavis.edu/~romik/teaching-pages/mat235a-2013/lecturenotes235A.pdf
For independent symmetric signs with coefficient squares `f n`, these are
the tail-probability and truncated-variance conditions in Kolmogorov's
three-series theorem. The truncated mean is zero. This module formalizes
the deterministic truncation equivalences, not the probability theorem.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace RiemannResearch.Analysis.NonnegativeEnergy

/-- Large squared-amplitude indicator at the energy cutoff c. -/
def largeTermIndicator (f : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  if c < f n then 1 else 0

/-- The complete energy of terms whose squared amplitude is at most c. -/
def truncatedEnergy (f : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  if f n ≤ c then f n else 0

/-- Exact clipping identity, including every small-term energy. -/
theorem clipped_eq_large_add_small (f : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    min (f n) c = c * largeTermIndicator f c n + truncatedEnergy f c n := by
  by_cases h : c < f n
  · simp [largeTermIndicator, truncatedEnergy, h, not_le_of_gt h,
      min_eq_right (le_of_lt h)]
  · have hle : f n ≤ c := le_of_not_gt h
    simp [largeTermIndicator, truncatedEnergy, h, hle]

/-- Any fixed positive energy cutoff preserves summability. -/
theorem summable_clipped_iff (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (c : ℝ) (hc : 0 < c) :
    Summable (fun n => min (f n) c) ↔ Summable f := by
  constructor
  · intro hs
    have he : ∀ᶠ n in atTop, min (f n) c < c :=
      (tendsto_order.1 hs.tendsto_atTop_zero).2 c hc
    apply hs.congr_atTop
    filter_upwards [he] with n hn
    have hfn : f n < c := (min_lt_iff.mp hn).resolve_right (lt_irrefl c)
    exact min_eq_left (le_of_lt hfn)
  · intro hs
    exact hs.of_nonneg_of_le (fun n => le_min (hf n) hc.le)
      (fun n => min_le_left (f n) c)

/-- The two nonzero deterministic conditions for a symmetric-sign series. -/
theorem summable_iff_tail_indicator_and_truncated_energy
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (c : ℝ) (hc : 0 < c) :
    Summable f ↔ Summable (largeTermIndicator f c) ∧
      Summable (truncatedEnergy f c) := by
  have hmin : ∀ n, 0 ≤ min (f n) c := fun n => le_min (hf n) hc.le
  constructor
  · intro hs
    have hclip := (summable_clipped_iff f hf c hc).mpr hs
    constructor
    · apply (hclip.mul_left c⁻¹).of_nonneg_of_le
      · intro n
        simp only [largeTermIndicator]
        split_ifs <;> positivity
      · intro n
        by_cases h : c < f n
        · simp [largeTermIndicator, h, min_eq_right (le_of_lt h), hc.ne']
        · simpa [largeTermIndicator, h] using mul_nonneg (inv_nonneg.mpr hc.le) (hmin n)
    · apply hclip.of_nonneg_of_le
      · intro n
        simp only [truncatedEnergy]
        split_ifs
        · exact hf n
        · exact le_rfl
      · intro n
        by_cases h : f n ≤ c
        · simp [truncatedEnergy, h]
        · simpa [truncatedEnergy, h] using hmin n
  · rintro ⟨hl, ht⟩
    apply (summable_clipped_iff f hf c hc).mp
    simpa only [← clipped_eq_large_add_small] using (hl.mul_left c).add ht

/-- An exact bounded-term formulation of nonnegative energy nonsummability. -/
theorem not_summable_iff_clipped_prefix_unbounded
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (c : ℝ) (hc : 0 < c) :
    ¬ Summable f ↔
      ∀ B : ℝ, ∃ N : ℕ, B < ∑ n ∈ Finset.range N, min (f n) c := by
  have hmin : ∀ n, 0 ≤ min (f n) c := fun n => le_min (hf n) hc.le
  constructor
  · intro hn
    have hnclip : ¬ Summable (fun n => min (f n) c) :=
      fun hs => hn ((summable_clipped_iff f hf c hc).mp hs)
    have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg hmin).mp hnclip
    intro B
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht) (B + 1))
    exact ⟨N, by linarith [hN N le_rfl]⟩
  · intro hu hs
    have hclip := (summable_clipped_iff f hf c hc).mpr hs
    obtain ⟨N, hN⟩ := hu (∑' n, min (f n) c)
    exact (not_lt_of_ge
      (hclip.sum_le_tsum (Finset.range N) (fun n hn => hmin n))) hN

end RiemannResearch.Analysis.NonnegativeEnergy
