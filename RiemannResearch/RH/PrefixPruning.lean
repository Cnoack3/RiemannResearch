/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimeSubtreeBudget

/-! # Exact finite-head pruning of the ascending prime tree

Edges beyond the physical head are either invisible or have a digit depending
only on their parent. Sum the signed weights of crossing siblings before taking
a positive part. The exact identity holds for arbitrary real node weights. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QPrimeSubtreeBudget
open ZetaTwoHilbert QSquarefreeDisplacementRigidity

/-- Sum of the weights of the edges crossing the cutoff from this parent. -/
def frontierMass (T : ℕ → ℝ) (H N k : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 H, if k = parent r ∧ N < r then T r else 0

/-- The common digit on every edge crossing the physical head from k. -/
def frontierDigit (k n : ℕ) : ℝ := (n : ℝ) - ((n % k : ℕ) : ℝ)

theorem frontierDigit_nonneg (k n : ℕ) : 0 ≤ frontierDigit k n := by
  unfold frontierDigit
  exact sub_nonneg.mpr (by exact_mod_cast Nat.mod_le n k)

theorem stepDigit_eq_frontierDigit {r n N : ℕ} (hn : n ≤ N) (hr : N < r) :
    stepDigit r n = frontierDigit (parent r) n := by
  simp only [stepDigit, frontierDigit, Nat.mod_eq_of_lt (hn.trans_lt hr)]

private theorem aggregate_frontier (T : ℕ → ℝ) (H N : ℕ) (a : ℕ → ℝ) :
    (∑ k ∈ Finset.range (N + 1), a k * frontierMass T H N k) =
      ∑ r ∈ Finset.Icc 2 H, if parent r ≤ N ∧ N < r then a (parent r) * T r else 0 := by
  unfold frontierMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : N < r
  · simp only [h, and_true, mul_ite, mul_zero]
    simp [Finset.mem_range]
  · simp [h]

/-- Exact aggregation on every site of a head, with no discarded error.
The first sum keeps internal edges. The boundary sum records one signed
mass per possible parent, independent of the number of crossing siblings. -/
theorem signed_pruned_identity (T : ℕ → ℝ) (H N n : ℕ) (hn : n ≤ N) :
    (∑ r ∈ Finset.Icc 2 H, stepDigit r n * T r) =
      (∑ r ∈ Finset.Icc 2 H, if r ≤ N then stepDigit r n * T r else 0) +
        ∑ k ∈ Finset.range (N + 1), frontierDigit k n * frontierMass T H N k := by
  rw [aggregate_frontier, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : r ≤ N
  · simp [hr, Nat.not_lt_of_ge hr]
  · have hr' : N < r := by omega
    rw [stepDigit_eq_frontierDigit hn hr']
    by_cases hp : parent r ≤ N
    · simp [hr, hr', hp]
    · have hk : n < parent r := by omega
      simp [hp, hr, frontierDigit, Nat.mod_eq_of_lt hk]

/-- Taking the bad sign only after pooling crossing siblings yields a
one-sided cost valid on the whole chosen head. -/
def prunedBudget (T : ℕ → ℝ) (σ : ℝ) (H N n : ℕ) : ℝ :=
  (∑ r ∈ Finset.Icc 2 H, if r ≤ N then stepDigit r n * max 0 (-σ * T r) else 0) +
    ∑ k ∈ Finset.range (N + 1),
      frontierDigit k n * max 0 (-σ * frontierMass T H N k)

theorem signed_le_prunedBudget (T : ℕ → ℝ) (σ : ℝ) (H N n : ℕ) (hn : n ≤ N) :
    -σ * (∑ r ∈ Finset.Icc 2 H, stepDigit r n * T r) ≤
      prunedBudget T σ H N n := by
  rw [signed_pruned_identity T H N n hn, mul_add, Finset.mul_sum, Finset.mul_sum]
  unfold prunedBudget
  apply add_le_add <;> apply Finset.sum_le_sum
  · intro r hr
    by_cases h : r ≤ N
    · simp only [if_pos h]
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (digit_bounds (Finset.mem_Icc.mp hr).1 n).1
    · simp [h]
  · intro k _
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (frontierDigit_nonneg k n)

private theorem bad_frontier_le (T : ℕ → ℝ) (σ : ℝ) (H N k : ℕ) :
    max 0 (-σ * frontierMass T H N k) ≤
      frontierMass (fun r => max 0 (-σ * T r)) H N k := by
  unfold frontierMass
  apply max_le
  · apply Finset.sum_nonneg
    intro r _
    split_ifs
    · exact le_max_left _ _
    · rfl
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    split_ifs
    · exact le_max_right _ _
    · simp

/-- Pooling is always at least as good as taking every edge sign first. -/
theorem prunedBudget_le_unpooled (T : ℕ → ℝ) (σ : ℝ) (H N n : ℕ) (hn : n ≤ N) :
    prunedBudget T σ H N n ≤
      ∑ r ∈ Finset.Icc 2 H, stepDigit r n * max 0 (-σ * T r) := by
  rw [signed_pruned_identity (fun r => max 0 (-σ * T r)) H N n hn]
  unfold prunedBudget
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left (bad_frontier_le T σ H N k) (frontierDigit_nonneg k n)

/-- Each head may choose its own arbitrarily late horizons. The sign and
upper bound are common over the physical sites. -/
theorem rh_of_pruned_subtree_budget (σ C : ℝ) (hσ : |σ| = 1) (hC : 0 ≤ C)
    (hb : ∀ n, ∃ᶠ H : ℕ in atTop,
      prunedBudget (subtree (charge displacement) H) σ H n n ≤ C) : RiemannHypothesis := by
  apply riemannHypothesis_of_one_sided_bounded_displacement σ C hσ hC
  intro n
  have ht := (signed_subtree_tendsto displacement n).const_mul (-σ)
  rw [neg_mul_neg] at ht
  by_contra! h
  have hg := ht.eventually (lt_mem_nhds h)
  obtain ⟨H, hH, hgt⟩ := ((hb n).and_eventually hg).exists
  exact (not_lt_of_ge ((signed_le_prunedBudget _ σ H n n le_rfl).trans hH)) hgt

end RiemannResearch.RH.QPrimeSubtreeBudget
