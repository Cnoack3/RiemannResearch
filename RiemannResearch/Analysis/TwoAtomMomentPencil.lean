import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

/-!
# Two isolated atoms from four moments

Source: §8 of the user-provided Mellin/prime-orbit PCC handoff. The
characteristic pencil of the two Hankel moment matrices recovers both atoms.
The hypothesis that the supplied moments come from two atoms is essential.
-/

namespace RiemannResearch.Analysis.TwoAtomMomentPencil

/-- Moment of a measure supported at the specified two locations. -/
noncomputable def moment (w₁ w₂ y₁ y₂ : ℝ) (j : ℕ) : ℝ := w₁ * y₁ ^ j + w₂ * y₂ ^ j

/-- Hankel moment matrix with offset d. Offsets zero and one use moments 0–3. -/
noncomputable def hankel (w₁ w₂ y₁ y₂ : ℝ) (d : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![moment w₁ w₂ y₁ y₂ d, moment w₁ w₂ y₁ y₂ (d + 1);
     moment w₁ w₂ y₁ y₂ (d + 1), moment w₁ w₂ y₁ y₂ (d + 2)]

/-- Exact determinant factorization of the generalized eigenvalue pencil. -/
theorem det_pencil (w₁ w₂ y₁ y₂ t : ℝ) :
    (hankel w₁ w₂ y₁ y₂ 1 - t • hankel w₁ w₂ y₁ y₂ 0).det =
      w₁ * w₂ * (y₂ - y₁)^2 * (y₁ - t) * (y₂ - t) := by
  simp [Matrix.det_fin_two, hankel, moment]
  ring

/-- For two different atoms of positive mass the generalized eigenvalues are exactly their locations. -/
theorem det_pencil_eq_zero_iff {w₁ w₂ y₁ y₂ t : ℝ}
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hy : y₁ ≠ y₂) :
    (hankel w₁ w₂ y₁ y₂ 1 - t • hankel w₁ w₂ y₁ y₂ 0).det = 0 ↔ t = y₁ ∨ t = y₂ := by
  rw [det_pencil]
  simp [mul_eq_zero, hw₁.ne', hw₂.ne', sub_ne_zero.mpr hy.symm, sub_eq_zero, eq_comm]

end RiemannResearch.Analysis.TwoAtomMomentPencil
