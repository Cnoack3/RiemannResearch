/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteSignedVariance
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite class fluctuations and weighted Dirichlet bounds

Source: direct finite Cauchy--Schwarz and square expansion, developed for
the user-directed rational-tail investigation, 20 October 2026.
These bounds keep the entire class variance. No asymptotic smallness is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteClassDirichlet
open RiemannResearch.Analysis.FiniteIncidenceTailCharge

theorem weighted_cauchy {α : Type*} (s : Finset α) (w x y : α → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) :
    (∑ a ∈ s, w a * x a * y a) ^ 2 ≤
      (∑ a ∈ s, w a * x a ^ 2) * ∑ a ∈ s, w a * y a ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun a ha => mul_nonneg (hw a ha) (sq_nonneg _))
    (fun a ha => mul_nonneg (hw a ha) (sq_nonneg _))
  intro a ha
  nlinarith [sq_nonneg (w a * x a * y a)]

/-- Exact pairwise representation of a centered class variance. -/
theorem centered_pairwise_identity {α : Type*} (s : Finset α) (x : α → ℝ)
    (c : ℝ) (hm : (∑ a ∈ s, (x a - c)) = 0) :
    (∑ a ∈ s, ∑ b ∈ s, (x a - x b) ^ 2) =
      2 * (s.card : ℝ) * ∑ a ∈ s, (x a - c) ^ 2 := by
  have hrow (a : α) :
      (∑ b ∈ s, (x a - x b) ^ 2) =
        (s.card : ℝ) * (x a - c) ^ 2 + ∑ b ∈ s, (x b - c) ^ 2 := by
    have he : (∑ b ∈ s, (x a - x b) ^ 2) =
        (s.card : ℝ) * (x a - c) ^ 2 + (∑ b ∈ s, (x b - c) ^ 2) -
          2 * (x a - c) * ∑ b ∈ s, (x b - c) := by
      have hc : (s.card : ℝ) * (x a - c) ^ 2 = ∑ b ∈ s, (x a - c) ^ 2 := by
        simp
      rw [hc, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    rw [he, hm, mul_zero, sub_zero]
  simp only [hrow, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul]
  ring

/-- A supplied pairwise resistance bound gives an explicit class Poincare bound. -/
theorem class_poincare {α : Type*} (s : Finset α) (x : α → ℝ)
    (c E : ℝ) (D : α → α → ℝ)
    (hm : (∑ a ∈ s, (x a - c)) = 0)
    (hp : ∀ a ∈ s, ∀ b ∈ s, (x a - x b) ^ 2 ≤ D a b * E) :
    2 * (s.card : ℝ) * (∑ a ∈ s, (x a - c) ^ 2) ≤
      (∑ a ∈ s, ∑ b ∈ s, D a b) * E := by
  rw [← centered_pairwise_identity s x c hm]
  calc
    _ ≤ ∑ a ∈ s, ∑ b ∈ s, D a b * E := by
      exact Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hp a ha b hb))
    _ = _ := by simp only [Finset.sum_mul]

/-- The negative-mass budget with the explicit pairwise path constant. -/
theorem negative_mass_poincare {α : Type*} (s : Finset α) (x : α → ℝ)
    (c E : ℝ) (D : α → α → ℝ)
    (hm : (∑ a ∈ s, x a) = (s.card : ℝ) * c)
    (hp : ∀ a ∈ s, ∀ b ∈ s, (x a - x b) ^ 2 ≤ D a b * E) :
    8 * negativeCharge s x * (negativeCharge s x + (s.card : ℝ) * c) ≤
      (∑ a ∈ s, ∑ b ∈ s, D a b) * E := by
  have hz : (∑ a ∈ s, (x a - c)) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hm, sub_self]
  have hP := class_poincare s x c E D hz hp
  have hN := negative_charge_quadratic_budget s x c hm
  linarith

/-- Exact completion of a finite dual quadratic objective. -/
theorem dual_square_identity {α : Type*} (s : Finset α) (w r x : α → ℝ)
    (hcross : (∑ a ∈ s, w a * r a * x a) = ∑ a ∈ s, w a * x a) :
    (∑ a ∈ s, w a * r a ^ 2) -
        (2 * (∑ a ∈ s, w a * x a) - ∑ a ∈ s, w a * x a ^ 2) =
      ∑ a ∈ s, w a * (r a - x a) ^ 2 := by
  rw [← hcross, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem dual_objective_le {α : Type*} (s : Finset α) (w r x : α → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hcross : (∑ a ∈ s, w a * r a * x a) = ∑ a ∈ s, w a * x a) :
    2 * (∑ a ∈ s, w a * x a) - (∑ a ∈ s, w a * x a ^ 2) ≤
      ∑ a ∈ s, w a * r a ^ 2 := by
  have he := dual_square_identity s w r x hcross
  have hn := Finset.sum_nonneg (s := s)
    (fun a ha => mul_nonneg (hw a ha) (sq_nonneg (r a - x a)))
  linarith

end RiemannResearch.Analysis.FiniteClassDirichlet
