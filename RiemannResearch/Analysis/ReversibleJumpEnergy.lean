/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact finite reversible jump energy and exit-rate control

Source: independent derivation for the user's prime-resampling RH agenda,
27 October 2026. The finite identity retains the signed cross term; diagonal
self-loops contribute zero. QReciprocalWeightedEnergy is the identified RH
consumer. Identification with the countable prime-resampling kernel is a
paper argument in PrimeResamplingResearch20261027.md.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ReversibleJumpEnergy

variable {α : Type*} [Fintype α]

/-- Symmetric weighted jump energy. Diagonal entries contribute zero. -/
def finiteJumpEnergy (W : α → α → ℝ) (g : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, ∑ y, W x y * (g x - g y) ^ 2

/-- Exact signed decomposition of the symmetric jump energy.
No nonnegativity hypothesis is needed for this algebraic identity. -/
theorem finiteJumpEnergy_eq_rate_square_sub_cross
    (W : α → α → ℝ) (g : α → ℝ)
    (hsym : ∀ x y, W x y = W y x) :
    finiteJumpEnergy W g =
      (∑ x, (∑ y, W x y) * (g x) ^ 2) -
        ∑ x, ∑ y, W x y * g x * g y := by
  have hfirst : (∑ x, ∑ y, W x y * (g x) ^ 2) =
      ∑ x, (∑ y, W x y) * (g x) ^ 2 := by
    apply Finset.sum_congr rfl
    intro x hx
    exact (Finset.sum_mul _ _ _).symm
  have hsecond : (∑ x, ∑ y, W x y * (g y) ^ 2) =
      ∑ x, (∑ y, W x y) * (g x) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    calc
      _ = ∑ y, W x y * (g x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hsym y x]
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hexpand : (∑ x, ∑ y, W x y * (g x - g y) ^ 2) =
      (∑ x, ∑ y, W x y * (g x) ^ 2) +
        (∑ x, ∑ y, W x y * (g y) ^ 2) -
          2 * ∑ x, ∑ y, W x y * g x * g y := by
    calc
      _ = ∑ x, ∑ y, (W x y * (g x) ^ 2 + W x y * (g y) ^ 2 -
          2 * (W x y * g x * g y)) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = _ := by
        simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hfirst, hsecond] at hexpand
  unfold finiteJumpEnergy
  linarith


/-- The universal symmetric-matrix estimate, before deleting diagonal mass. -/
theorem finiteJumpEnergy_le_twice_total_rate
    (W : α → α → ℝ) (g : α → ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (hsym : ∀ x y, W x y = W y x) :
    finiteJumpEnergy W g ≤ 2 * ∑ x, (∑ y, W x y) * (g x) ^ 2 := by
  have hfirst : (∑ x, ∑ y, W x y * (g x) ^ 2) =
      ∑ x, (∑ y, W x y) * (g x) ^ 2 := by
    apply Finset.sum_congr rfl
    intro x hx
    exact (Finset.sum_mul _ _ _).symm
  have hsecond : (∑ x, ∑ y, W x y * (g y) ^ 2) =
      ∑ x, (∑ y, W x y) * (g x) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    calc
      _ = ∑ y, W x y * (g x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hsym y x]
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hpoint (x y : α) :
      W x y * (g x - g y) ^ 2 ≤
        2 * (W x y * (g x) ^ 2) + 2 * (W x y * (g y) ^ 2) := by
    have hs : (g x - g y) ^ 2 ≤ 2 * (g x) ^ 2 + 2 * (g y) ^ 2 := by
      nlinarith [sq_nonneg (g x + g y)]
    have hm := mul_le_mul_of_nonneg_left hs (hW x y)
    nlinarith
  have hsum :
      (∑ x, ∑ y, W x y * (g x - g y) ^ 2) ≤
      ∑ x, ∑ y, (2 * (W x y * (g x) ^ 2) +
        2 * (W x y * (g y) ^ 2)) := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro y hy
    exact hpoint x y
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hfirst, hsecond] at hsum
  unfold finiteJumpEnergy
  linarith

/-- Remove the stationary self-loop probability from the jump weight. -/
def offDiagonalWeight (W : α → α → ℝ) (x y : α) : ℝ := by
  classical
  exact if x = y then 0 else W x y

/-- Weighted exit mass at a state, excluding self-loops. -/
def finiteExitRate (W : α → α → ℝ) (x : α) : ℝ :=
  ∑ y, offDiagonalWeight W x y

theorem finiteJumpEnergy_offDiagonal (W : α → α → ℝ) (g : α → ℝ) :
    finiteJumpEnergy (offDiagonalWeight W) g = finiteJumpEnergy W g := by
  classical
  unfold finiteJumpEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hxy : x = y
  · subst y
    simp [offDiagonalWeight]
  · simp [offDiagonalWeight, hxy]

/-- Sharp exit-rate control for a finite reversible jump form. -/
theorem finiteJumpEnergy_le_twice_exit_rate
    (W : α → α → ℝ) (g : α → ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (hsym : ∀ x y, W x y = W y x) :
    finiteJumpEnergy W g ≤ 2 * ∑ x, finiteExitRate W x * (g x) ^ 2 := by
  classical
  have hOff : ∀ x y, 0 ≤ offDiagonalWeight W x y := by
    intro x y
    by_cases hxy : x = y
    · simp [offDiagonalWeight, hxy]
    · simpa [offDiagonalWeight, hxy] using hW x y
  have hOffsym : ∀ x y, offDiagonalWeight W x y = offDiagonalWeight W y x := by
    intro x y
    by_cases hxy : x = y
    · subst y
      rfl
    · simp [offDiagonalWeight, hxy, Ne.symm hxy, hsym x y]
  have h := finiteJumpEnergy_le_twice_total_rate
    (offDiagonalWeight W) g hOff hOffsym
  rw [finiteJumpEnergy_offDiagonal] at h
  exact h

/-- A bounded exit rate gives an ordinary weighted L² estimate. -/
theorem finiteJumpEnergy_le_of_exit_rate_le
    (W : α → α → ℝ) (g μ : α → ℝ) (C : ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (hsym : ∀ x y, W x y = W y x)
    (hrate : ∀ x, finiteExitRate W x ≤ C * μ x) :
    finiteJumpEnergy W g ≤ 2 * C * ∑ x, μ x * (g x) ^ 2 := by
  have h := finiteJumpEnergy_le_twice_exit_rate W g hW hsym
  have hs : (∑ x, finiteExitRate W x * (g x) ^ 2) ≤
      ∑ x, (C * μ x) * (g x) ^ 2 := by
    apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_right (hrate x) (sq_nonneg _)
  have he : (∑ x, (C * μ x) * (g x) ^ 2) =
      C * ∑ x, μ x * (g x) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [he] at hs
  linarith

/-- A geometric resampling coordinate leaves its present value with this
probability.  It is bounded by the nonzero-valuation indicator plus q. -/
theorem geometric_resampling_exit_le (q : ℝ) (k : ℕ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    1 - (1 - q) * q ^ k ≤ (if k = 0 then 0 else 1) + q := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [if_neg hk]
    have hp := mul_nonneg (sub_nonneg.mpr hq1) (pow_nonneg hq0 k)
    linarith


end RiemannResearch.Analysis.ReversibleJumpEnergy
