/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ArithmeticProgressionSquareTail
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Complete arithmetic-progression reciprocal-square tails

This passes the checked elementary finite telescoping estimate to an actual
convergent infinite series.  Summability is proved from nonnegative bounded
partial sums; it is not an added hypothesis or a zero-by-nonsummability fallback.
The Mathlib bounded-partial-sum interface is standard monotone convergence.
-/
noncomputable section
namespace RiemannResearch.Analysis.ArithmeticProgressionSquareTail
open scoped BigOperators

theorem progression_tail_summable (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    Summable (fun k : ℕ => 1 / (a + ((k + 1 : ℕ) : ℝ) * L) ^ 2) := by
  apply summable_of_sum_range_le
  · intro k
    positivity
  · exact finite_tail_bound a L ha hL

theorem complete_tail_bound (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    (∑' k : ℕ, 1 / (a + ((k + 1 : ℕ) : ℝ) * L) ^ 2) ≤ 1 / (L * a) := by
  exact (progression_tail_summable a L ha hL).tsum_le_of_sum_range_le
    (finite_tail_bound a L ha hL)

theorem shifted_progression_summable (r L : ℝ) (hr : 0 < r) (hL : 0 < L)
    (N : ℕ) :
    Summable (fun k : ℕ => 1 / (r + ((k + N + 1 : ℕ) : ℝ) * L) ^ 2) := by
  have hx : 0 < r + (N : ℝ) * L := by positivity
  have heq : (fun k : ℕ => 1 / (r + ((k + N + 1 : ℕ) : ℝ) * L) ^ 2) =
      (fun k : ℕ => 1 / ((r + (N : ℝ) * L) + ((k + 1 : ℕ) : ℝ) * L) ^ 2) := by
    funext k
    have harg : r + ((k + N + 1 : ℕ) : ℝ) * L =
        (r + (N : ℝ) * L) + ((k + 1 : ℕ) : ℝ) * L := by push_cast; ring
    rw [harg]
  rw [heq]
  exact progression_tail_summable (r + (N : ℝ) * L) L hx hL

theorem complete_shifted_tail_bound (r L : ℝ) (hr : 0 < r) (hL : 0 < L)
    (N : ℕ) :
    (∑' k : ℕ, 1 / (r + ((k + N + 1 : ℕ) : ℝ) * L) ^ 2) ≤
      1 / (L * (r + (N : ℝ) * L)) := by
  have hx : 0 < r + (N : ℝ) * L := by positivity
  have heq : (fun k : ℕ => 1 / (r + ((k + N + 1 : ℕ) : ℝ) * L) ^ 2) =
      (fun k : ℕ => 1 / ((r + (N : ℝ) * L) + ((k + 1 : ℕ) : ℝ) * L) ^ 2) := by
    funext k
    have harg : r + ((k + N + 1 : ℕ) : ℝ) * L =
        (r + (N : ℝ) * L) + ((k + 1 : ℕ) : ℝ) * L := by push_cast; ring
    rw [harg]
  rw [heq]
  exact complete_tail_bound (r + (N : ℝ) * L) L hx hL

theorem full_progression_summable (r L : ℝ) (hr : 0 < r) (hL : 0 < L) :
    Summable (fun k : ℕ => 1 / (r + (k : ℝ) * L) ^ 2) :=
  Summable.comp_nat_add (f := fun k : ℕ => 1 / (r + (k : ℝ) * L) ^ 2)
    (k := 1) (progression_tail_summable r L hr hL)

end RiemannResearch.Analysis.ArithmeticProgressionSquareTail
