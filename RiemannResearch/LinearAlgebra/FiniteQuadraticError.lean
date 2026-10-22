/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Ring

/-!
# Entrywise bounds for finite quadratic expressions

An entrywise real matrix error bounds every quadratic direction by the error
times the squared sum of coefficient norms. No symmetry or positivity is
assumed. RH consumer: ArithmeticScrewCellBounds.

Source: user-provided handoff v16 motivates certified matrix errors; the proof
uses finite-sum triangle inequalities.
-/

namespace RiemannResearch.LinearAlgebra
open scoped BigOperators
noncomputable section

/-- Entrywise enclosures give an all-directions quadratic error bound. -/
theorem quadratic_error_of_entrywise_bound {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (ε : ℝ) (h : ∀ i j, ‖A i j - B i j‖ ≤ ε) (s : ι → ℝ) :
    ‖dotProduct s (A.mulVec s) - dotProduct s (B.mulVec s)‖ ≤
      ε * (∑ i, ‖s i‖)^2 := by
  have he : dotProduct s (A.mulVec s) - dotProduct s (B.mulVec s) =
      ∑ i, ∑ j, s i * (A i j - B i j) * s j := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_sub, sub_mul,
      Finset.sum_sub_distrib, mul_assoc]
  rw [he]
  calc
    _ ≤ ∑ i, ∑ j, ‖s i * (A i j - B i j) * s j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ j, ‖s i‖ * ε * ‖s j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (h i j) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring
end
end RiemannResearch.LinearAlgebra
