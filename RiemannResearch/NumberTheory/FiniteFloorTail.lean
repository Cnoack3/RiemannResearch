import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

/-!
# Finite floor tails and positive arithmetic prefixes

Source: user-provided Pareto sublinear-energy argument, 2026-09-22.
The identities implement its finite double-counting step. Their concrete
consumer is the canonical Möbius window estimate.
-/

open scoped BigOperators

namespace RiemannResearch.NumberTheory

/-- Count a finite floor tail by swapping the divisor and occurrence indices. -/
theorem finite_floor_tail_swap (a : ℕ → ℝ) (Y n : ℕ) :
    (∑ d ∈ Finset.Icc (Y+1) n, a d * ((n/d:ℕ):ℝ)) =
      ∑ k ∈ Finset.Icc 1 (n/(Y+1)), ∑ d ∈ Finset.Icc (Y+1) (n/k), a d := by
  classical
  have hcount (d : ℕ) (hd : d ∈ Finset.Icc (Y+1) n) :
      ((n/d:ℕ):ℝ) = ∑ k ∈ Finset.Icc 1 (n/(Y+1)), if k*d ≤ n then (1:ℝ) else 0 := by
    have hdp : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
    have hdq : n/d ≤ n/(Y+1) := by
      apply (Nat.le_div_iff_mul_le (Nat.succ_pos Y)).mpr
      exact (Nat.mul_le_mul_left (n/d) (Finset.mem_Icc.mp hd).1).trans (Nat.div_mul_le_self n d)
    have hs : (Finset.Icc 1 (n/(Y+1))).filter (fun k => k*d ≤ n) = Finset.Icc 1 (n/d) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      rw [← Nat.le_div_iff_mul_le hdp]
      omega
    rw [← Finset.sum_filter, hs]
    simp
  calc
    _ = ∑ d ∈ Finset.Icc (Y+1) n, a d *
        (∑ k ∈ Finset.Icc 1 (n/(Y+1)), if k*d ≤ n then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hcount d hd]
    _ = ∑ k ∈ Finset.Icc 1 (n/(Y+1)), ∑ d ∈ Finset.Icc (Y+1) n,
        if k*d ≤ n then a d else 0 := by
      simp_rw [Finset.mul_sum, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkp : 0 < k := (Finset.mem_Icc.mp hk).1
      have hs : (Finset.Icc (Y+1) n).filter (fun d => k*d ≤ n) =
          Finset.Icc (Y+1) (n/k) := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_Icc]
        have he : k*d ≤ n ↔ d ≤ n/k := by
          rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le hkp]
        rw [he]
        have hkn := Nat.div_le_self n k
        omega
      rw [← Finset.sum_filter, hs]

/-- Split a positive arithmetic prefix at an intermediate integer cutoff. -/
theorem positive_prefix_split_at (a : ℕ → ℝ) (Y n : ℕ) (hYn : Y ≤ n) :
    (∑ d ∈ Finset.Icc 1 n, a d) =
      (∑ d ∈ Finset.Icc 1 Y, a d) + ∑ d ∈ Finset.Icc (Y+1) n, a d := by
  classical
  have hu : Finset.Icc 1 n = Finset.Icc 1 Y ∪ Finset.Icc (Y+1) n := by
    ext d
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hd : Disjoint (Finset.Icc 1 Y) (Finset.Icc (Y+1) n) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    simp only [Finset.mem_Icc] at hd1 hd2
    omega
  rw [hu, Finset.sum_union hd]

end RiemannResearch.NumberTheory
