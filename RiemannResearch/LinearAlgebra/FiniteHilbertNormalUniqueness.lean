/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import Mathlib.Tactic.Linarith

/-!
# Synthesis uniqueness for singular finite normal systems

Source: user-provided measure-change regularity handoff, A1.
Coefficient uniqueness is not assumed or asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.LinearAlgebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

theorem finiteSchurCombination_eq_of_normal (y : E) (a : ι → E)
    (c d : ι → ℝ)
    (hc : ∀ i, inner ℝ (a i) (finiteSchurCombination a c) = inner ℝ (a i) y)
    (hd : ∀ i, inner ℝ (a i) (finiteSchurCombination a d) = inner ℝ (a i) y) :
    finiteSchurCombination a c = finiteSchurCombination a d := by
  have hz (i : ι) : inner ℝ (a i)
      (finiteSchurCombination a c - finiteSchurCombination a d) = 0 := by
    rw [inner_sub_right, hc i, hd i, sub_self]
  have hs (b : ι → ℝ) : inner ℝ (finiteSchurCombination a b)
      (finiteSchurCombination a c - finiteSchurCombination a d) = 0 := by
    change inner ℝ (∑ i, b i • a i)
      (finiteSchurCombination a c - finiteSchurCombination a d) = 0
    simp only [sum_inner, real_inner_smul_left, hz, mul_zero, Finset.sum_const_zero]
  have hnorm : ‖finiteSchurCombination a c - finiteSchurCombination a d‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, hs c, hs d, sub_self]
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith))

end RiemannResearch.LinearAlgebra
