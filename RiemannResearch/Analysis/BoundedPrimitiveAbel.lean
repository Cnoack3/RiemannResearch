import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signed Abel summation and bounded primitives

Source: user-provided wavelet argument, analytic_wavelet_foothold.md, §4.
This is the discrete exact identity used before estimating signed wavelet
interactions. Both endpoint terms are retained before taking a limit.
-/

namespace RiemannResearch.Analysis
open scoped BigOperators
open Filter

/-- Exact finite summation by parts, with both signed endpoint terms. -/
theorem boundedPrimitive_abel_identity (B f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (B (k+1) - B k) * f k) =
      B N * f N - B 0 * f 0 +
        ∑ k ∈ Finset.range N, B (k+1) * (f k - f (k+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

private theorem sum_forward_difference (f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (f k - f (k+1))) = f 0 - f N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

/-- A primitive in [0,C] controls each signed weighted interval by C times
its initial weight. No absolute values are taken inside the sum. -/
theorem boundedPrimitive_weighted_interval_bound (B f : ℕ → ℝ) (C : ℝ)
    (N : ℕ) (hB : ∀ k, 0 ≤ B k ∧ B k ≤ C)
    (hf : ∀ k, 0 ≤ f k) (hmono : Antitone f) :
    |∑ k ∈ Finset.range N, (B (k+1)-B k) * f k| ≤ C * f 0 := by
  have hdiff (k : ℕ) : 0 ≤ f k - f (k+1) := sub_nonneg.mpr (hmono (Nat.le_succ k))
  have hlo : 0 ≤ B N * f N +
      ∑ k ∈ Finset.range N, B (k+1) * (f k-f (k+1)) := by
    exact add_nonneg (mul_nonneg (hB N).1 (hf N))
      (Finset.sum_nonneg fun k _ => mul_nonneg (hB (k+1)).1 (hdiff k))
  have hsum : (∑ k ∈ Finset.range N, B (k+1) * (f k-f (k+1))) ≤
      C * (f 0-f N) := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, C * (f k-f (k+1)) := by
        exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hB (k+1)).2 (hdiff k)
      _ = C * (f 0-f N) := by rw [← Finset.mul_sum, sum_forward_difference]
  have hhi : B N * f N +
      (∑ k ∈ Finset.range N, B (k+1) * (f k-f (k+1))) ≤ C * f 0 := by
    have h := mul_le_mul_of_nonneg_right (hB N).2 (hf N)
    nlinarith
  have h0lo := mul_nonneg (hB 0).1 (hf 0)
  have h0hi := mul_le_mul_of_nonneg_right (hB 0).2 (hf 0)
  rw [boundedPrimitive_abel_identity]
  apply abs_le.mpr
  constructor <;> linarith

/-- Complete signed identity, when the ordinary summability and endpoint
limit conditions hold. Neither continuous nor discrete remainder is discarded. -/
theorem boundedPrimitive_abel_tsum (B f : ℕ → ℝ)
    (hleft : Summable (fun k => (B (k+1)-B k) * f k))
    (hright : Summable (fun k => B (k+1) * (f k-f (k+1))))
    (hend : Tendsto (fun N => B N * f N) atTop (nhds 0)) :
    (∑' k, (B (k+1)-B k) * f k) =
      -B 0 * f 0 + ∑' k, B (k+1) * (f k-f (k+1)) := by
  have hr := (hend.sub_const (B 0 * f 0)).add hright.hasSum.tendsto_sum_nat
  have heq :
      (fun N => ∑ k ∈ Finset.range N, (B (k+1)-B k) * f k) =
      (fun N => B N * f N - B 0 * f 0 +
        ∑ k ∈ Finset.range N, B (k+1) * (f k-f (k+1))) := by
    funext N
    exact boundedPrimitive_abel_identity B f N
  have hl := hleft.hasSum.tendsto_sum_nat
  rw [heq] at hl
  simpa only [zero_sub, neg_mul] using tendsto_nhds_unique hl hr

end RiemannResearch.Analysis
