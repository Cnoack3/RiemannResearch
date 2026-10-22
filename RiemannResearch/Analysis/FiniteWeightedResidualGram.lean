/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Part of the RiemannResearch project.
Authors: Christian Noack
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

-- The Apache-specific header convention does not determine project licensing.
set_option linter.style.header false

/-!
# Complete weighted finite-head residual Gram expansion

Source: independently assembled from the user's exact squarefree regression
continuation, October 2026. The identity retains the signed linear term and
every quadratic mixed term. It requires no sign assumptions on weights or
coefficients. The concrete consumer is RH/SquarefreeResidualHeadGram.lean.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis

/-- Exact expansion, without sign assumptions on weights or coefficients. -/
theorem weighted_finite_head_square_expansion
    {ι κ : Type*} [Fintype ι] (A : Finset κ)
    (w : κ → ℝ) (c : ι → ℝ) (v : ι → κ → ℝ) :
    (∑ k ∈ A, w k * (1 - ∑ i, c i * v i k) ^ 2) =
      (∑ k ∈ A, w k) -
        2 * (∑ i, c i * (∑ k ∈ A, w k * v i k)) +
        ∑ i, ∑ j, c i * c j * (∑ k ∈ A, w k * v i k * v j k) := by
  classical
  have hcross :
      (∑ k ∈ A, w k * (∑ i, c i * v i k)) =
        ∑ i, c i * (∑ k ∈ A, w k * v i k) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsquare (k : κ) :
      (∑ i, c i * v i k) ^ 2 =
        ∑ i, ∑ j, (c i * v i k) * (c j * v j k) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hquad :
      (∑ k ∈ A, w k * (∑ i, c i * v i k) ^ 2) =
        ∑ i, ∑ j, c i * c j * (∑ k ∈ A, w k * v i k * v j k) := by
    simp_rw [hsquare, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ = ∑ k ∈ A,
        (w k - 2 * (w k * (∑ i, c i * v i k)) +
          w k * (∑ i, c i * v i k) ^ 2) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (∑ k ∈ A, w k) -
        2 * (∑ k ∈ A, w k * (∑ i, c i * v i k)) +
        (∑ k ∈ A, w k * (∑ i, c i * v i k) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = _ := by rw [hcross, hquad]

end RiemannResearch.Analysis
