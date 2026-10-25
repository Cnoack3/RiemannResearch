/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reciprocal-energy sums and a positive approximation gap

These scalar consequences apply when a legal weighted average has squared error
at most `1 / S + c / S ^ 2`, and `δ` is a lower bound for every legal error.
The averaging construction and the arithmetic interpretation of `δ` are separate
inputs: this module supplies no unconditional capacity limit.
-/

namespace RiemannResearch.Analysis.ReciprocalEnergyGap

/-- Clear the positive reciprocal-energy denominator in an error-gap bound. -/
theorem gap_mul_sq_le {δ S c : ℝ} (hS : 0 < S)
    (h : δ ≤ 1 / S + c / S ^ 2) : δ * S ^ 2 ≤ S + c := by
  calc
    δ * S ^ 2 ≤ (1 / S + c / S ^ 2) * S ^ 2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg S)
    _ = S + c := by field_simp [ne_of_gt hS]

/-- A positive gap uniformly bounds reciprocal-energy sums. -/
theorem reciprocal_sum_le_max {δ S c : ℝ} (hδ : 0 < δ)
    (hS : 0 < S) (hc : 0 ≤ c) (h : δ ≤ 1 / S + c / S ^ 2) :
    S ≤ max 1 ((1 + c) / δ) := by
  by_cases hs : S ≤ 1
  · exact hs.trans (le_max_left _ _)
  have hs1 : 1 ≤ S := le_of_lt (lt_of_not_ge hs)
  have hcS : c ≤ c * S := by nlinarith
  have hquad := gap_mul_sq_le hS h
  have hlinear : δ * S ≤ 1 + c := by
    by_contra! hgt
    have hp := mul_pos (sub_pos.mpr hgt) hS
    nlinarith [hquad, hcS]
  have hb : S ≤ (1 + c) / δ := (le_div_iff₀ hδ).2 (by nlinarith)
  exact hb.trans (le_max_right _ _)

/-- Cofinality of the reciprocal-energy sums excludes any positive gap. -/
theorem gap_nonpos_of_reciprocal_cofinal {δ c : ℝ} (S : ℕ → ℝ)
    (hc : 0 ≤ c) (hS : ∀ n, 0 < S n)
    (h : ∀ n, δ ≤ 1 / S n + c / (S n) ^ 2)
    (hlarge : ∀ R : ℝ, ∃ n, R ≤ S n) : δ ≤ 0 := by
  by_contra hn
  have hδ : 0 < δ := lt_of_not_ge hn
  obtain ⟨n, hn⟩ := hlarge (max 1 ((1 + c) / δ) + 1)
  have hb := reciprocal_sum_le_max hδ (hS n) hc (h n)
  linarith

/-- A nonnegative gap vanishes if the controlled reciprocal-energy sums are
cofinal. The cofinality hypothesis is not established by this theorem. -/
theorem gap_eq_zero_of_reciprocal_cofinal {δ c : ℝ} (S : ℕ → ℝ)
    (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hS : ∀ n, 0 < S n)
    (h : ∀ n, δ ≤ 1 / S n + c / (S n) ^ 2)
    (hlarge : ∀ R : ℝ, ∃ n, R ≤ S n) : δ = 0 := by
  exact le_antisymm (gap_nonpos_of_reciprocal_cofinal S hc hS h hlarge) hδ

end RiemannResearch.Analysis.ReciprocalEnergyGap
