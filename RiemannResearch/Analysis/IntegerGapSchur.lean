/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MarkedFourierTail
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Inverse-cube Schur estimates for distinct integer indices.
Source: user-provided MontgomeryGammaAudit20261110.md, Section 5.
The finite telescoping remainder is retained before the uniform bound. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.IntegerGapSchur

theorem inverse_cube_tail_le {x : ℝ} (hx : 1 ≤ x) :
    1 / (x+1)^3 ≤ 1 / (2*x ^ 2) - 1 / (2*(x+1)^2) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x+1 := by linarith
  have he : 1 / (2*x ^ 2) - 1 / (2*(x+1)^2) =
      (2*x+1) / (2*x ^ 2*(x+1)^2) := by field_simp; ring
  rw [he]
  apply (div_le_div_iff₀ (pow_pos hx1 3) (by positivity)).mpr
  nlinarith [mul_nonneg (sq_nonneg (x+1)) (by linarith : 0 ≤ 3*x+1)]

theorem tail_sum_with_remainder (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / ((k : ℝ)+2)^3) ≤
      1/2 - 1/(2*((N : ℝ)+1)^2) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    have h := inverse_cube_tail_le (x := (N : ℝ)+1) (by linarith [Nat.cast_nonneg (α := ℝ) N])
    rw [Finset.sum_range_succ]
    push_cast
    convert! add_le_add ih h using 1 <;> ring

theorem cube_sum_le (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / ((k : ℝ)+1)^3) ≤ 3/2 := by
  cases N with
  | zero => norm_num
  | succ N =>
    rw [Finset.sum_range_succ']
    have he : (∑ k ∈ Finset.range N, 1 / (((k+1:ℕ):ℝ)+1)^3) =
        ∑ k ∈ Finset.range N, 1 / ((k : ℝ)+2)^3 := by
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      ring
    rw [he]
    norm_num
    have h := tail_sum_with_remainder N
    have hn : 0 ≤ 1/(2*((N : ℝ)+1)^2) := by positivity
    simp only [one_div] at h hn
    linarith

def weight (n m : ℕ) : ℝ := 1 / |(n : ℝ)-(m : ℝ)|^3

theorem weight_nonneg (n m : ℕ) : 0 ≤ weight n m := by unfold weight; positivity
theorem weight_symm (n m : ℕ) : weight n m = weight m n := by
  simp [weight, abs_sub_comm]
@[simp] theorem weight_self (n : ℕ) : weight n n = 0 := by simp [weight]

theorem left_sum_eq (n : ℕ) :
    (∑ m ∈ Finset.range n, weight n m) =
      ∑ k ∈ Finset.range n, 1 / ((k : ℝ)+1)^3 := by
  rw [← Finset.sum_range_reflect (weight n) n]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n := Finset.mem_range.mp hk
  have hle : n-1-k ≤ n := by omega
  have hd : n-(n-1-k) = k+1 := by omega
  unfold weight
  rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hle)), ← Nat.cast_sub hle, hd]
  push_cast
  rfl

theorem right_weight (n k : ℕ) : weight n (n+1+k) = 1 / ((k : ℝ)+1)^3 := by
  have he : (n : ℝ)-((n+1+k:ℕ):ℝ) = -((k : ℝ)+1) := by push_cast; ring
  rw [weight, he, abs_neg, abs_of_pos (by positivity)]

theorem range_row_le {n D : ℕ} (hn : n ≤ D) :
    (∑ m ∈ Finset.range (D+1), weight n m) ≤ 3 := by
  have hd : D+1 = (n+1)+(D-n) := by omega
  rw [hd, Finset.sum_range_add, Finset.sum_range_succ, weight_self, add_zero, left_sum_eq]
  simp_rw [right_weight]
  linarith [cube_sum_le n, cube_sum_le (D-n)]

theorem row_le (s : Finset ℕ) {n D : ℕ} (hn : n ≤ D)
    (hD : ∀ m ∈ s, m ≤ D) : (∑ m ∈ s, weight n m) ≤ 3 := by
  calc
    _ ≤ ∑ m ∈ Finset.range (D+1), weight n m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hD m hm))
      · intro m hm hms; exact weight_nonneg n m
    _ ≤ 3 := range_row_le hn

theorem quadratic_le (s : Finset ℕ) (c : ℕ → ℂ) (K : ℕ → ℕ → ℂ)
    {D : ℕ} {B : ℝ} (hB : 0 ≤ B) (hD : ∀ n ∈ s, n ≤ D)
    (hK : ∀ n ∈ s, ∀ m ∈ s, ‖K n m‖ ≤ B * weight n m) :
    ‖∑ n ∈ s, ∑ m ∈ s, c n * conj (c m) * K n m‖ ≤
      3 * B * ∑ n ∈ s, ‖c n‖^2 := by
  have hquad : (∑ n ∈ s, ∑ m ∈ s, weight n m * ‖c n‖ * ‖c m‖) ≤
      3 * ∑ n ∈ s, ‖c n‖^2 := by
    apply MarkedFourierTail.symmetric_kernel_quadratic_le_row_bound s (fun n => ‖c n‖) weight 3
    · intro n hn m hm; exact weight_nonneg n m
    · intro n hn m hm; exact weight_symm n m
    · intro n hn; exact row_le s (hD n hn) hD
  calc
    _ ≤ ∑ n ∈ s, ‖∑ m ∈ s, c n * conj (c m) * K n m‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s, ∑ m ∈ s, B * (weight n m * ‖c n‖ * ‖c m‖) := by
      apply Finset.sum_le_sum
      intro n hn
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, norm_mul, Complex.norm_conj]
      calc
        _ ≤ (‖c n‖*‖c m‖)*(B*weight n m) :=
          mul_le_mul_of_nonneg_left (hK n hn m hm) (by positivity)
        _ = _ := by ring
    _ = B * ∑ n ∈ s, ∑ m ∈ s, weight n m * ‖c n‖ * ‖c m‖ := by
      simp only [Finset.mul_sum]
    _ ≤ B * (3 * ∑ n ∈ s, ‖c n‖^2) := mul_le_mul_of_nonneg_left hquad hB
    _ = _ := by ring

end RiemannResearch.Analysis.IntegerGapSchur
