import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring

/-!
# Determinant of a one-point extension

Source: user-requested fourth Ramanujan transfer program, October 2026.
The reusable result is the ordinary Schur determinant identity with the
adjoined point indexed by `none`; its Mellin consumer keeps the old finite
test indexing unchanged.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RiemannResearch.LinearAlgebra
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]

theorem det_option_schur (M : Matrix (Option ι) (Option ι) K)
    (hA : IsUnit (M.submatrix some some).det) :
    M.det = (M.submatrix some some).det *
      (M none none - ∑ i, M none (some i) *
        (∑ j, ((M.submatrix some some)⁻¹) i j *
          M (some j) none)) := by
  let A : Matrix ι ι K := M.submatrix some some
  let B : Matrix ι Unit K := Matrix.replicateCol Unit (fun i => M (some i) none)
  let C : Matrix Unit ι K := Matrix.replicateRow Unit (fun i => M none (some i))
  let D : Matrix Unit Unit K := fun _ _ => M none none
  let e : Option ι ≃ ι ⊕ Unit :=
    { toFun := fun i => i.elim (Sum.inr ()) Sum.inl
      invFun := fun i => i.elim some (fun _ => none)
      left_inv := by intro i; cases i <;> rfl
      right_inv := by intro i; cases i with
        | inl i => rfl
        | inr i => cases i; rfl }
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hA
  have hM : Matrix.reindex e e M = Matrix.fromBlocks A B C D := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [← Matrix.det_reindex_self e M, hM, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv, Matrix.det_unique (n := Unit)]
  change A.det * (M none none - ((C * A⁻¹) * B) () ()) = _
  congr 1
  congr 1
  simp only [Matrix.mul_apply, C, B, Matrix.replicateRow_apply,
    Matrix.replicateCol_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [A, Finset.mul_sum, mul_assoc]

end RiemannResearch.LinearAlgebra
