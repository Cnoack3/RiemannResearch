import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Exact defect in adding separately optimized scalar Schur complements

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`,
Section 5, nonlinearity warning. The formula uses the ordinary scalar
Schur expression directly and retains the discrepancy between the two
separate optimizers. The counterexample has two positive-definite blocks.
-/

namespace RiemannResearch.LinearAlgebra

/-- Combining Gram contributions before minimization leaves this exact
square defect over the sum of separately minimized Schur values. -/
theorem scalarSchur_addition_defect (g₁ g₂ b₁ b₂ c₁ c₂ : ℝ)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (hgs : g₁ + g₂ ≠ 0) :
    ((c₁ + c₂) - (b₁ + b₂) ^ 2 / (g₁ + g₂)) -
      ((c₁ - b₁ ^ 2 / g₁) + (c₂ - b₂ ^ 2 / g₂)) =
        (g₂ * b₁ - g₁ * b₂) ^ 2 / (g₁ * g₂ * (g₁ + g₂)) := by
  field_simp [hg₁, hg₂, hgs]
  ring

/-- Schur nonadditivity already occurs for two strictly positive-definite
real symmetric blocks: [[1,1],[1,2]] and [[1,-1],[-1,2]]. -/
theorem scalarSchur_nonadditive_positive_example :
    ∃ g₁ g₂ b₁ b₂ c₁ c₂ : ℝ,
      0 < g₁ ∧ 0 < g₂ ∧
      0 < c₁ - b₁ ^ 2 / g₁ ∧ 0 < c₂ - b₂ ^ 2 / g₂ ∧
      ((c₁ + c₂) - (b₁ + b₂) ^ 2 / (g₁ + g₂)) ≠
        ((c₁ - b₁ ^ 2 / g₁) + (c₂ - b₂ ^ 2 / g₂)) := by
  refine ⟨1, 1, 1, -1, 2, 2, ?_⟩
  norm_num

end RiemannResearch.LinearAlgebra
