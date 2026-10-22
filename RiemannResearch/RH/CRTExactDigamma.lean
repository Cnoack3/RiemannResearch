/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTTrigammaBounds

/-!
# Exact digamma progression identities and strict positivity

The quantities L and M remain the original convergent arithmetic series.
Digamma has no global positive sign; trigamma is positive on the positive axis.
These results use actual `Complex.digamma`, not new special-function axioms.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.CRTBlock
noncomputable section
open Pareto

def realDigamma (x : ℝ) : ℝ := (Complex.digamma (x : ℂ)).re

theorem hasSum_progression_reciprocal_difference
    {Q a b : ℝ} (hQ : 0 < Q) (ha : 0 < a) (hb : 0 < b) :
    HasSum (fun k : ℕ => 1 / (Q * k + a) - 1 / (Q * k + b))
      ((realDigamma (b / Q) - realDigamma (a / Q)) / Q) := by
  have h := ((hasSum_reciprocal_difference_positive (div_pos ha hQ)).sub
    (hasSum_reciprocal_difference_positive (div_pos hb hQ))).mul_left (1 / Q)
  convert h using 1 <;> try rfl
  · funext k
    have h0 : Q ≠ 0 := ne_of_gt hQ
    have h1 : Q * (k : ℝ) + a ≠ 0 := by positivity
    have h2 : Q * (k : ℝ) + b ≠ 0 := by positivity
    have h3 : (k : ℝ) + a / Q ≠ 0 := by positivity
    have h4 : (k : ℝ) + b / Q ≠ 0 := by positivity
    field_simp
    <;> ring
  · unfold realDigamma
    ring

theorem lKernel_reciprocal_difference {t : ℝ} (ht : 0 < t) :
    lKernel t = (1 / t - 1 / (t + 1)) - (1 / (t + 1) - 1 / (t + 2)) := by
  have h0 : t ≠ 0 := ne_of_gt ht
  have h1 : t + 1 ≠ 0 := by positivity
  have h2 : t + 2 ≠ 0 := by positivity
  unfold lKernel
  field_simp
  <;> ring

/-- Exact equality: no absolute values or one-sided replacements of L. -/
theorem progressionL_eq_digamma {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    progressionL Q r =
      (2 * realDigamma ((r + 1) / Q) - realDigamma (r / Q) -
        realDigamma ((r + 2) / Q)) / Q := by
  have h := (hasSum_progression_reciprocal_difference hQ hr
    (show 0 < r + 1 by positivity)).sub
      (hasSum_progression_reciprocal_difference hQ
        (show 0 < r + 1 by positivity) (show 0 < r + 2 by positivity))
  have hs : HasSum (fun k : ℕ => lKernel (Q * k + r))
      ((2 * realDigamma ((r + 1) / Q) - realDigamma (r / Q) -
        realDigamma ((r + 2) / Q)) / Q) := by
    convert h using 1 <;> try rfl
    · funext k
      simpa only [add_assoc] using
        lKernel_reciprocal_difference (show 0 < Q * (k : ℝ) + r by positivity)
    · ring
  exact hs.tsum_eq

theorem mKernel_exact {t : ℝ} (ht : 0 < t) :
    lKernel t / t = 1 / t^2 - (1 / t - 1 / (t + 1)) - lKernel t / 2 := by
  have h0 : t ≠ 0 := ne_of_gt ht
  have h1 : t + 1 ≠ 0 := by positivity
  have h2 : t + 2 ≠ 0 := by positivity
  unfold lKernel
  field_simp
  <;> ring

/-- Exact M formula, with the same L retained rather than estimated. -/
theorem progressionM_eq_trigamma_digamma {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    progressionM Q r = trigamma (r / Q) / Q^2 -
      (realDigamma ((r + 1) / Q) - realDigamma (r / Q)) / Q -
        progressionL Q r / 2 := by
  have h := ((progressionSquare_summable hQ hr).hasSum.sub
    (hasSum_progression_reciprocal_difference hQ hr
      (show 0 < r + 1 by positivity))).sub
        ((progressionL_summable hQ hr).hasSum.div_const 2)
  have hs : HasSum (fun k : ℕ => lKernel (Q * k + r) / (Q * k + r))
      (progressionSquare Q r -
        (realDigamma ((r + 1) / Q) - realDigamma (r / Q)) / Q -
          progressionL Q r / 2) := by
    convert h using 1 <;> try rfl
    · funext k
      simpa only [add_assoc] using
        mKernel_exact (show 0 < Q * (k : ℝ) + r by positivity)
  rw [← progressionSquare_eq_trigamma hQ hr]
  exact hs.tsum_eq

theorem trigamma_pos {x : ℝ} (hx : 0 < x) : 0 < trigamma x := by
  rw [trigamma_eq_series hx]
  exact (reciprocalSquareSeries_summable_pos hx).tsum_pos
    (fun k => by positivity) 0 (by positivity)

theorem trigamma_strictAntiOn : StrictAntiOn trigamma (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  rw [trigamma_eq_series hx, trigamma_eq_series hy]
  apply Summable.tsum_lt_tsum (i := 0)
  · intro k
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [Nat.cast_nonneg k (α := ℝ)]
  · simp only [Nat.cast_zero, zero_add]
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  · exact reciprocalSquareSeries_summable_pos hy
  · exact reciprocalSquareSeries_summable_pos hx

theorem progressionL_pos {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    0 < progressionL Q r := by
  exact (progressionL_summable hQ hr).tsum_pos
    (fun k => lKernel_nonneg (by positivity)) 0 (by simp [lKernel]; positivity)

theorem progressionM_pos {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    0 < progressionM Q r := by
  exact (progressionM_summable hQ hr).tsum_pos
    (fun k => by unfold lKernel; positivity) 0 (by simp [lKernel]; positivity)

theorem lKernel_le_progressionL {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    lKernel r ≤ progressionL Q r := by
  have h := (progressionL_summable hQ hr).sum_le_tsum ({0} : Finset ℕ)
    (fun k _ => lKernel_nonneg (by positivity))
  simpa [progressionL] using h

theorem mKernel_le_progressionM {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    lKernel r / r ≤ progressionM Q r := by
  have h := (progressionM_summable hQ hr).sum_le_tsum ({0} : Finset ℕ)
    (fun k _ => by unfold lKernel; positivity)
  simpa [progressionM] using h

/-- A finite prefix plus the very same exact digamma tail, at any cutoff. -/
theorem progressionL_prefix_exact {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r)
    (N : ℕ) :
    progressionL Q r = (∑ k ∈ Finset.range N, lKernel (Q * k + r)) +
      progressionL Q (Q * N + r) := by
  have h := (progressionL_summable hQ hr).sum_add_tsum_nat_add N
  simpa only [progressionL, Nat.cast_add, mul_add, add_assoc, add_left_comm,
    add_comm] using h.symm

end
end RiemannResearch.RH.CRTBlock
