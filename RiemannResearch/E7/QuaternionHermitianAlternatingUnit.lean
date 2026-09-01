/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianDiagonalQuadraticPair

/-!
# An explicit alternating unit for a diagonal degree-eight adjoint algebra

For the adjoint involution attached to the hermitian Gram matrix `diag(1,z)`,
this file constructs

`X = [[0,z],[-1,0]]`

together with the explicit two-sided inverse

`X⁻¹ = [[0,-1],[z⁻¹,0]]`.

The matrix is skew-adjoint.  More strongly, it lies in
`Alt(A,star) = range (id - star)`: the upper-triangular matrix
`Y = [[0,z],[0,0]]` satisfies `Y - star Y = X`.  This direct witness does
not divide by two, so the alternating statement itself is
characteristic-independent.

An invertible alternating element is the object used to define the
discriminant of an orthogonal involution.  This file constructs that object
but deliberately does not assert a reduced-norm, discriminant, or generalized
Clifford-component calculation.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u v

/-- Membership in `Alt(A,star) = range (id - star)`. -/
def IsAlternatingElement {A : Type v} [Sub A] [Star A] (x : A) : Prop :=
  ∃ y : A, y - star y = x

section DiagonalUnit

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]

/-- The matrix `[[0,z],[-1,0]]` in the adjoint algebra of `diag(1,z)`. -/
def diagonalAlternatingMatrix
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    DegreeEightAlgebra p q :=
  !![0, z.val; -1, 0]

/-- The explicit inverse `[[0,-1],[z⁻¹,0]]` of
`diagonalAlternatingMatrix`. -/
def diagonalAlternatingInverseMatrix
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    DegreeEightAlgebra p q :=
  !![0, -1; z.inv, 0]

/-- An explicit preimage of `diagonalAlternatingMatrix` under
`id - star`. -/
def diagonalAlternatingPreimageMatrix
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    DegreeEightAlgebra p q :=
  !![0, z.val; 0, 0]

@[simp] theorem diagonalAlternatingMatrix_mul_inverse
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    diagonalAlternatingMatrix p q z *
        diagonalAlternatingInverseMatrix p q z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalAlternatingMatrix, diagonalAlternatingInverseMatrix,
      Matrix.mul_apply, z.val_mul_inv]

@[simp] theorem diagonalAlternatingInverseMatrix_mul
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    diagonalAlternatingInverseMatrix p q z *
        diagonalAlternatingMatrix p q z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalAlternatingMatrix, diagonalAlternatingInverseMatrix,
      Matrix.mul_apply, z.inv_mul_val]

/-- The displayed matrix is skew under the adjoint involution of
`diag(1,z)`. -/
@[simp] theorem diagonalAlternatingMatrix_adjoint
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    HermitianGram.adjoint (diagonalDegreeEightGram p q z)
        (diagonalAlternatingMatrix p q z) =
      -diagonalAlternatingMatrix p q z := by
  apply (diagonalDegreeEightAdjoint_eq_neg_iff p q z
    (diagonalAlternatingMatrix p q z)).2
  simp [diagonalAlternatingMatrix, z.star_val, z.inv_mul_val]

/-- The upper-triangular preimage has alternating difference exactly equal to
the displayed skew matrix. -/
@[simp] theorem diagonalAlternatingPreimageMatrix_sub_adjoint
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    diagonalAlternatingPreimageMatrix p q z -
        HermitianGram.adjoint (diagonalDegreeEightGram p q z)
          (diagonalAlternatingPreimageMatrix p q z) =
      diagonalAlternatingMatrix p q z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalAlternatingPreimageMatrix, diagonalAlternatingMatrix,
      z.star_val, z.inv_mul_val]

/-- An explicit invertible skew-adjoint element in the degree-eight adjoint
algebra attached to `diag(1,z)`. -/
def diagonalAlternatingSkewAdjointUnit
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    SkewAdjointUnit (A := DiagonalDegreeEightAdjointAlgebra p q z) where
  val := ⟨diagonalAlternatingMatrix p q z⟩
  inv := ⟨diagonalAlternatingInverseMatrix p q z⟩
  val_mul_inv := by
    apply AdjointAlgebra.ext
    exact diagonalAlternatingMatrix_mul_inverse p q z
  inv_mul_val := by
    apply AdjointAlgebra.ext
    exact diagonalAlternatingInverseMatrix_mul p q z
  star_val := by
    apply AdjointAlgebra.ext
    exact diagonalAlternatingMatrix_adjoint p q z

@[simp] theorem diagonalAlternatingSkewAdjointUnit_val
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    (diagonalAlternatingSkewAdjointUnit p q z).val.val =
      diagonalAlternatingMatrix p q z := rfl

@[simp] theorem diagonalAlternatingSkewAdjointUnit_inv
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    (diagonalAlternatingSkewAdjointUnit p q z).inv.val =
      diagonalAlternatingInverseMatrix p q z := rfl

/-- The concrete upper-triangular preimage, regarded as an element of the
adjoint algebra. -/
def diagonalAlternatingPreimage
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    DiagonalDegreeEightAdjointAlgebra p q z :=
  ⟨diagonalAlternatingPreimageMatrix p q z⟩

@[simp] theorem diagonalAlternatingPreimage_val
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    (diagonalAlternatingPreimage p q z).val =
      diagonalAlternatingPreimageMatrix p q z := rfl

/-- The explicit preimage realizes the skew unit as an alternating
difference. -/
@[simp] theorem diagonalAlternatingPreimage_sub_star
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    diagonalAlternatingPreimage p q z -
        star (diagonalAlternatingPreimage p q z) =
      (diagonalAlternatingSkewAdjointUnit p q z).val := by
  apply AdjointAlgebra.ext
  exact diagonalAlternatingPreimageMatrix_sub_adjoint p q z

/-- The explicit two-sided unit belongs to `Alt(A,star)`, with no
characteristic restriction. -/
theorem diagonalAlternatingSkewAdjointUnit_isAlternatingElement
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    IsAlternatingElement (diagonalAlternatingSkewAdjointUnit p q z).val :=
  ⟨diagonalAlternatingPreimage p q z,
    diagonalAlternatingPreimage_sub_star p q z⟩

end DiagonalUnit

end RiemannResearch.E7.QuaternionHermitian
