/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
Elementary rational telescoping domination underlying the complete residue-tail
certificate. This avoids any special-function asymptotics and any integration.
The `finite_tail_bound` theorem bounds every partial sum; an infinite-series
bridge can use nonnegativity and convergence of increasing partial sums.
-/
noncomputable section
namespace RiemannResearch.Analysis.ArithmeticProgressionSquareTail
open scoped BigOperators

theorem reciprocal_square_step_le (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    1 / (a + L) ^ 2 ≤ (1 / a - 1 / (a + L)) / L := by
  have haL : 0 < a + L := add_pos ha hL
  calc
    1 / (a + L) ^ 2 ≤ 1 / (a * (a + L)) := by
      apply one_div_le_one_div_of_le (mul_pos ha haL)
      nlinarith [mul_pos hL haL]
    _ = (1 / a - 1 / (a + L)) / L := by
      field_simp [ne_of_gt ha, ne_of_gt hL, ne_of_gt haL]
      ring

theorem finite_tail_telescoping (a L : ℝ) (ha : 0 < a) (hL : 0 < L) (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / (a + ((k + 1 : ℕ) : ℝ) * L) ^ 2) ≤
      (1 / a - 1 / (a + (N : ℝ) * L)) / L := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hx : 0 < a + (N : ℝ) * L := by positivity
      have hstep := reciprocal_square_step_le (a + (N : ℝ) * L) L hx hL
      have heq : a + ((N + 1 : ℕ) : ℝ) * L = a + (N : ℝ) * L + L := by
        push_cast
        ring
      rw [Finset.sum_range_succ]
      calc
        _ ≤ (1 / a - 1 / (a + (N : ℝ) * L)) / L +
            (1 / (a + (N : ℝ) * L) - 1 / (a + (N : ℝ) * L + L)) / L := by
          exact add_le_add ih (by simpa only [heq] using hstep)
        _ = _ := by rw [heq]; ring

theorem finite_tail_bound (a L : ℝ) (ha : 0 < a) (hL : 0 < L) (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / (a + ((k + 1 : ℕ) : ℝ) * L) ^ 2) ≤
      1 / (L * a) := by
  have hx : 0 < a + (N : ℝ) * L := by positivity
  calc
    _ ≤ (1 / a - 1 / (a + (N : ℝ) * L)) / L :=
      finite_tail_telescoping a L ha hL N
    _ ≤ (1 / a) / L := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hL)
      exact sub_le_self _ (le_of_lt (one_div_pos.mpr hx))
    _ = _ := by ring

end RiemannResearch.Analysis.ArithmeticProgressionSquareTail
