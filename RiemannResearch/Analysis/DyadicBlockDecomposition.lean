/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Complete scaled dyadic block decomposition

The block with index `j` contains all integers from `N * 2^j` through
`N * 2^(j+1) - 1`. Finite telescoping and cofinality establish an exact
decomposition of a complete nonnegative summable series beyond its initial
head. No block or terminal term is discarded.

This extends the elementary finite accounting in
`Analysis.DyadicWeightedContrast` to arbitrary positive starting scales.
The intended consumer is the complete Cesàro cumulative-sum energy.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.DyadicBlockDecomposition

/-- Sum of one complete dyadic block beginning at the scale `N`. -/
def scaledDyadicBlock (a : ℕ → ℝ) (N j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N * 2 ^ j), a (N * 2 ^ j + i)

/-- Exact finite accounting, including the omitted initial head. -/
theorem sum_scaledDyadicBlock (a : ℕ → ℝ) (N J : ℕ) :
    (∑ j ∈ Finset.range J, scaledDyadicBlock a N j) =
      (∑ n ∈ Finset.range (N * 2 ^ J), a n) -
        ∑ n ∈ Finset.range N, a n := by
  unfold scaledDyadicBlock
  induction J with
  | zero => simp
  | succ J ih =>
      have hp : N * 2 ^ (J + 1) = N * 2 ^ J + N * 2 ^ J := by
        rw [pow_succ]
        ring
      rw [Finset.sum_range_succ, ih, hp, Finset.sum_range_add]
      ring

theorem scaledDyadicBlock_nonneg (a : ℕ → ℝ) (N j : ℕ)
    (ha : ∀ n, 0 ≤ a n) :
    0 ≤ scaledDyadicBlock a N j := by
  exact Finset.sum_nonneg (fun i _ => ha (N * 2 ^ j + i))

/-- Grouping a nonnegative summable series into complete blocks preserves
summability, including the degenerate scale `N = 0`. -/
theorem summable_scaledDyadicBlock (a : ℕ → ℝ) (N : ℕ)
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) :
    Summable (scaledDyadicBlock a N) := by
  refine summable_of_sum_range_le (c := ∑' n, a n)
    (fun j => scaledDyadicBlock_nonneg a N j ha) ?_
  intro J
  rw [sum_scaledDyadicBlock]
  exact (sub_le_self _ (Finset.sum_nonneg (fun n _ => ha n))).trans
    (hs.sum_le_tsum (Finset.range (N * 2 ^ J)) (fun n _ => ha n))

/-- The endpoints of the blocks are cofinal whenever the starting scale is
positive. -/
theorem tendsto_scaledDyadicEndpoint (N : ℕ) (hN : 0 < N) :
    Tendsto (fun J : ℕ => N * 2 ^ J) atTop atTop := by
  have hp (J : ℕ) : J ≤ 2 ^ J := by
    induction J with
    | zero => simp
    | succ J ih =>
        have hpos : 0 < (2 : ℕ) ^ J := pow_pos (by norm_num) J
        rw [pow_succ]
        omega
  have hb (J : ℕ) : J ≤ N * 2 ^ J := by
    apply (hp J).trans
    have hN1 : 1 ≤ N := hN
    simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ J) hN1
  exact tendsto_atTop_mono hb tendsto_id

/-- Exact complete regrouping: the block sum is precisely the total series
minus the finite head. -/
theorem tsum_scaledDyadicBlock (a : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) :
    (∑' j, scaledDyadicBlock a N j) =
      (∑' n, a n) - ∑ n ∈ Finset.range N, a n := by
  have hend := tendsto_scaledDyadicEndpoint N hN
  have ht := (hs.hasSum.tendsto_sum_nat.comp hend).sub_const
    (∑ n ∈ Finset.range N, a n)
  apply tendsto_nhds_unique
    (summable_scaledDyadicBlock a N ha hs).hasSum.tendsto_sum_nat
  simpa only [sum_scaledDyadicBlock, Function.comp_def] using ht

end RiemannResearch.Analysis.DyadicBlockDecomposition
