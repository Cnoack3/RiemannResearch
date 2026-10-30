/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertConstraints
import Mathlib.Tactic.Linarith

/-! Exact finite Gram trial certificates. Source: the user-provided RH
research handoff of 30 October 2026, Section 4.1, using the existing
capacity completion identity. No asymptotic estimate is asserted. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHilbertGram
open FiniteHilbertConstraints FiniteGramCapacity
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem capacity_eq_inverseGram {v : ι → H} (hv : LinearIndependent ℝ v)
    (s : ι → ℝ) :
    capacity hv s = dotProduct s ((gramMatrix v)⁻¹.mulVec s) := by
  rw [gramMatrix_inverseSource hv]
  unfold capacity dotProduct
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- Exact dual trial certificate, including its nonnegative loss. -/
theorem inverseGram_trial_completion {v : ι → H} (hv : LinearIndependent ℝ v)
    (s t : ι → ℝ) :
    dotProduct s ((gramMatrix v)⁻¹.mulVec s) -
      (2 * dotProduct t s - dotProduct t ((gramMatrix v).mulVec t)) =
      ‖minimumVector hv s - Fintype.linearCombination ℝ v t‖ ^ 2 := by
  have hc := capacity_completion hv s t
  rw [gramMatrix_quadratic, capacity_eq_inverseGram] at hc
  change 2 * dotProduct t s - _ = _ at hc
  linarith

theorem inverseGram_trial_lower {v : ι → H} (hv : LinearIndependent ℝ v)
    (s t : ι → ℝ) :
    2 * dotProduct t s - dotProduct t ((gramMatrix v).mulVec t) ≤
      dotProduct s ((gramMatrix v)⁻¹.mulVec s) := by
  have h := inverseGram_trial_completion hv s t
  nlinarith [sq_nonneg ‖minimumVector hv s - Fintype.linearCombination ℝ v t‖]

/-- Optimize over a prescribed single coefficient pattern. -/
theorem inverseGram_direction_lower {v : ι → H} (hv : LinearIndependent ℝ v)
    (s w : ι → ℝ) (hw : 0 < dotProduct w ((gramMatrix v).mulVec w)) :
    (dotProduct w s) ^ 2 / dotProduct w ((gramMatrix v).mulVec w) ≤
      dotProduct s ((gramMatrix v)⁻¹.mulVec s) := by
  have h := source_sq_le_capacity_mul_energy hv s w
  rw [gramMatrix_quadratic, capacity_eq_inverseGram] at h
  exact (div_le_iff₀ hw).mpr h
end RiemannResearch.Analysis.FiniteHilbertGram
