import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open scoped BigOperators

/-!
# Exact finite Pareto energy for an affine head

Source: the continuation of the user-provided
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Sections 25--26, recorded in `RH/TailCapacityLiteratureAudit20260919.md`.
The concrete RH consumer is the primorial Mobius sieve with head `1 - c * k`.
These lemmas verify its energy obstruction once that head identity is supplied.
The primorial specialization and its asymptotic arithmetic estimates are not
formalized here.

Bagchi, Theorem 1, https://arxiv.org/abs/math/0607733, supports the choice of
the weighted sequence norm; the finite-sum proofs below are elementary.
-/

namespace RiemannResearch.Analysis

/-- Exact finite energy of an affine physical head, retaining its mixed term. -/
theorem finite_pareto_affine_energy (c : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (1 - c * ((k : ℝ) + 1)) ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) =
    (N : ℝ) / ((N : ℝ) + 1) + c ^ 2 * (N : ℝ) -
      (2 * c + c ^ 2) * (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

/-- Exact finite error energy when the residual has physical value `c * k`. -/
theorem finite_pareto_linear_energy (c : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (c * ((k : ℝ) + 1)) ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) =
    c ^ 2 * ((N : ℝ) - (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 2))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

/-- The finite head contributes this much to any summable full error energy. -/
theorem pareto_affine_head_error_lower (f : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (hhead : ∀ k < N, f (k + 1) = 1 - c * ((k : ℝ) + 1))
    (hs : Summable (fun k : ℕ =>
      (1 - f (k + 1)) ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)))) :
    c ^ 2 * ((N : ℝ) - (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 2))) ≤
      ∑' k : ℕ, (1 - f (k + 1)) ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  calc
    _ = ∑ k ∈ Finset.range N,
        (c * ((k : ℝ) + 1)) ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) :=
      (finite_pareto_linear_energy c N).symm
    _ = ∑ k ∈ Finset.range N,
        (1 - f (k + 1)) ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hhead k (Finset.mem_range.mp hk)]
      ring
    _ ≤ _ := Summable.sum_le_tsum (Finset.range N) (fun k _ => by positivity) hs

/-- A coarse lower bound useful for disproving bounded energy of a proposed family. -/
theorem pareto_affine_head_error_lower_linear (f : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (hhead : ∀ k < N, f (k + 1) = 1 - c * ((k : ℝ) + 1))
    (hs : Summable (fun k : ℕ =>
      (1 - f (k + 1)) ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)))) :
    c ^ 2 * (N : ℝ) / 2 ≤
      ∑' k : ℕ, (1 - f (k + 1)) ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  have hsum : (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 2)) ≤ (N : ℝ) / 2 := by
    calc
      _ ≤ ∑ _k ∈ Finset.range N, (1 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        exact one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) k])
      _ = _ := by simp [div_eq_mul_inv]
  apply le_trans _ (pareto_affine_head_error_lower f c N hhead hs)
  convert mul_le_mul_of_nonneg_left (sub_le_sub_left hsum (N : ℝ)) (sq_nonneg c) using 1
  ring


end RiemannResearch.Analysis
