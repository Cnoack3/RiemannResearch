/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFiniteSupportDualCriterion
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact coordinate-head interpolation energy

Source: the user-requested reciprocal-head investigation, 7 November 2026.
The proof generalizes the repository's
QSquarefreeExactHeadResidualBarrier.exact_head_residual_completion from the
constant squarefree target to arbitrary targets and orthogonal tests.
All norm-square remainders are retained. No density or RH input is assumed.
The saved module is subject to the repository server verification gate.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QFiniteSupportDualCriterion
open ZetaTwoHilbert

/-- Head agreement and one exact orthogonality identity determine a signed tail pairing. -/
theorem matching_head_tail_pairing (N : ℕ) (x F r : QHilbert)
    (ho : inner ℝ r F = 0)
    (hh : ∀ n < N, F n = x n) :
    inner ℝ (F - finiteHead N x) (r - finiteHead N r) =
      -inner ℝ r (finiteHead N x) := by
  have hmatch (u : QHilbert) : inner ℝ F (finiteHead N u) =
      inner ℝ x (finiteHead N u) := by
    rw [inner_finiteHead_eq_sum, inner_finiteHead_eq_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hh n (Finset.mem_range.mp hn)]
  have hp : inner ℝ (finiteHead N r) (F - finiteHead N x) = 0 := by
    rw [real_inner_comm, inner_sub_left, hmatch, finiteHead_inner,
      finiteHead_idem, sub_self]
  rw [real_inner_comm, inner_sub_left, hp, sub_zero, inner_sub_right, ho, zero_sub]

/-- Complete head interpolation energy, retaining the orthogonal norm-square remainder. -/
theorem matching_head_residual_completion (N : ℕ) (x F r : QHilbert)
    (ho : inner ℝ r F = 0)
    (hh : ∀ n < N, F n = x n)
    (ht : ‖r - finiteHead N r‖ ^ 2 ≠ 0) :
    let h := finiteHead N x
    let t := r - finiteHead N r
    let a := inner ℝ r h
    ‖F‖ ^ 2 = ‖h‖ ^ 2 + a ^ 2 / ‖t‖ ^ 2 +
      ‖F - h + (a / ‖t‖ ^ 2) • t‖ ^ 2 := by
  dsimp only
  have hmatch (u : QHilbert) : inner ℝ F (finiteHead N u) =
      inner ℝ x (finiteHead N u) := by
    rw [inner_finiteHead_eq_sum, inner_finiteHead_eq_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hh n (Finset.mem_range.mp hn)]
  have hhead : inner ℝ F (finiteHead N x) = ‖finiteHead N x‖ ^ 2 := by
    rw [hmatch]
    have hi := finiteHead_inner N x (finiteHead N x)
    rw [finiteHead_idem, real_inner_self_eq_norm_sq] at hi
    exact hi.symm
  have hsplit : ‖F‖ ^ 2 = ‖finiteHead N x‖ ^ 2 + ‖F - finiteHead N x‖ ^ 2 := by
    rw [norm_sub_sq_real, hhead]
    ring
  have hpair := matching_head_tail_pairing N x F r ho hh
  have hshift :
      ‖F - finiteHead N x +
        (inner ℝ r (finiteHead N x) / ‖r - finiteHead N r‖ ^ 2) •
          (r - finiteHead N r)‖ ^ 2 =
      ‖F - finiteHead N x‖ ^ 2 -
        (inner ℝ r (finiteHead N x)) ^ 2 / ‖r - finiteHead N r‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right, hpair]
    have htnorm : ‖r - finiteHead N r‖ ≠ 0 := by
      intro hz
      apply ht
      rw [hz]
      norm_num
    field_simp [ht, htnorm]
    ring
  linarith

theorem matching_head_energy_lower (N : ℕ) (x F r : QHilbert)
    (ho : inner ℝ r F = 0)
    (hh : ∀ n < N, F n = x n)
    (ht : ‖r - finiteHead N r‖ ^ 2 ≠ 0) :
    ‖finiteHead N x‖ ^ 2 +
      (inner ℝ r (finiteHead N x)) ^ 2 / ‖r - finiteHead N r‖ ^ 2 ≤
      ‖F‖ ^ 2 := by
  have h := matching_head_residual_completion N x F r ho hh ht
  dsimp only at h
  nlinarith [sq_nonneg ‖F - finiteHead N x +
    (inner ℝ r (finiteHead N x) / ‖r - finiteHead N r‖ ^ 2) •
      (r - finiteHead N r)‖]

/-- The sharp signed head pairing controls the complete repair tail. -/
theorem matching_head_pairing_bound (N : ℕ) (x F r : QHilbert)
    (ho : inner ℝ r F = 0)
    (hh : ∀ n < N, F n = x n) :
    |inner ℝ r (finiteHead N x)| ≤
      ‖F - finiteHead N x‖ * ‖r - finiteHead N r‖ := by
  have h := abs_real_inner_le_norm (F - finiteHead N x) (r - finiteHead N r)
  rw [matching_head_tail_pairing N x F r ho hh, abs_neg] at h
  exact h

end RiemannResearch.RH.QFiniteSupportDualCriterion
