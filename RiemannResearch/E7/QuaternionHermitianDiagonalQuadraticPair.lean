/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianSymmetricSkewDecomposition
import Mathlib.Tactic.FinCases

/-!
# Diagonal degree-eight quadratic pairs

This file keeps the diagonal hermitian coefficient arbitrary.  Given an
invertible self-adjoint element `z` of the biquaternion algebra, it constructs
the degree-eight quadratic pair attached to `diag(1,z)` and calculates its
adjoint involution entry by entry.

For a matrix `X`, the formula is

`X ↦ [[star X₀₀, star X₁₀ * z],
      [z⁻¹ * star X₀₁, z⁻¹ * star X₁₁ * z]]`.

It also constructs the explicit invertible skew-adjoint matrix

`[[0,z],[-1,0]]`,

with inverse `[[0,-1],[z⁻¹,0]]`.  This is an actual alternating witness in
characteristic different from two and is the concrete input needed for a
future reduced-norm/discriminant calculation.

The remaining E7 realization problem is still to choose `z` so that the
discriminant and generalized Clifford components carry the required third
quaternion class.  No such invariant calculation is asserted here.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]

/-- The degree-eight quadratic pair attached to an arbitrary invertible
self-adjoint diagonal coefficient. -/
noncomputable def diagonalDegreeEightQuadraticPair_of_nondegenerate
    (p q : QuaternionParameters k) [NeZero (2 : k)]
    (z : SelfAdjointUnit (A := Biquaternion p q))
    (hp₃ : p.c₃ ≠ 0) (hpdisc : 4 * p.c₁ + p.c₂ ^ 2 ≠ 0)
    (hq₃ : q.c₃ ≠ 0) (hqdisc : 4 * q.c₁ + q.c₂ ^ 2 ≠ 0) :
    DegreeEightQuadraticPair k
      (DiagonalDegreeEightAdjointAlgebra p q z) :=
  (degreeEightCentralSimpleOrthogonalPair_of_nondegenerate
    p q (diagonalDegreeEightGram p q z)
    hp₃ hpdisc hq₃ hqdisc).toQuadraticPair

/-- The upper-left entry of the adjoint involution for `diag(1,z)`. -/
@[simp] theorem diagonalDegreeEightAdjoint_zero_zero
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q))
    (X : DegreeEightAlgebra p q) :
    (diagonalDegreeEightGram p q z).adjoint X 0 0 =
      star (X 0 0) := by
  simp [HermitianGram.adjoint, diagonalDegreeEightGram,
    HermitianGram.diagonalTwo, Matrix.mul_apply, Fin.sum_univ_two]

/-- The upper-right entry of the adjoint involution for `diag(1,z)`. -/
@[simp] theorem diagonalDegreeEightAdjoint_zero_one
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q))
    (X : DegreeEightAlgebra p q) :
    (diagonalDegreeEightGram p q z).adjoint X 0 1 =
      star (X 1 0) * z.val := by
  simp [HermitianGram.adjoint, diagonalDegreeEightGram,
    HermitianGram.diagonalTwo, Matrix.mul_apply, Fin.sum_univ_two]

/-- The lower-left entry of the adjoint involution for `diag(1,z)`. -/
@[simp] theorem diagonalDegreeEightAdjoint_one_zero
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q))
    (X : DegreeEightAlgebra p q) :
    (diagonalDegreeEightGram p q z).adjoint X 1 0 =
      z.inv * star (X 0 1) := by
  simp [HermitianGram.adjoint, diagonalDegreeEightGram,
    HermitianGram.diagonalTwo, Matrix.mul_apply, Fin.sum_univ_two]

/-- The lower-right entry of the adjoint involution for `diag(1,z)`. -/
@[simp] theorem diagonalDegreeEightAdjoint_one_one
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q))
    (X : DegreeEightAlgebra p q) :
    (diagonalDegreeEightGram p q z).adjoint X 1 1 =
      z.inv * star (X 1 1) * z.val := by
  simp [HermitianGram.adjoint, diagonalDegreeEightGram,
    HermitianGram.diagonalTwo, Matrix.mul_apply, Fin.sum_univ_two]

/-- A matrix is fixed by the diagonal adjoint involution exactly when its four
entries satisfy the displayed conjugation equations. -/
theorem diagonalDegreeEightAdjoint_eq_iff
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q))
    (X : DegreeEightAlgebra p q) :
    (diagonalDegreeEightGram p q z).adjoint X = X ↔
      star (X 0 0) = X 0 0 ∧
      star (X 1 0) * z.val = X 0 1 ∧
      z.inv * star (X 0 1) = X 1 0 ∧
      z.inv * star (X 1 1) * z.val = X 1 1 := by
  constructor
  · intro h
    constructor
    · simpa using congrArg (fun M => M 0 0) h
    constructor
    · simpa using congrArg (fun M => M 0 1) h
    constructor
    · simpa using congrArg (fun M => M 1 0) h
    · simpa using congrArg (fun M => M 1 1) h
  · rintro ⟨h00, h01, h10, h11⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h00
    · simpa using h01
    · simpa using h10
    · simpa using h11

/-- A matrix is skew-fixed by the diagonal adjoint involution exactly when
its four entries satisfy the corresponding negative equations. -/
theorem diagonalDegreeEightAdjoint_eq_neg_iff
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q))
    (X : DegreeEightAlgebra p q) :
    (diagonalDegreeEightGram p q z).adjoint X = -X ↔
      star (X 0 0) = -X 0 0 ∧
      star (X 1 0) * z.val = -X 0 1 ∧
      z.inv * star (X 0 1) = -X 1 0 ∧
      z.inv * star (X 1 1) * z.val = -X 1 1 := by
  constructor
  · intro h
    constructor
    · simpa using congrArg (fun M => M 0 0) h
    constructor
    · simpa using congrArg (fun M => M 0 1) h
    constructor
    · simpa using congrArg (fun M => M 1 0) h
    · simpa using congrArg (fun M => M 1 1) h
  · rintro ⟨h00, h01, h10, h11⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h00
    · simpa using h01
    · simpa using h10
    · simpa using h11

/-- The antidiagonal matrix used as an intrinsic discriminant witness for the
quadratic pair attached to `diag(1,z)`. -/
def diagonalSkewMatrix
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    DegreeEightAlgebra p q :=
  !![0, z.val; -1, 0]

/-- The explicit two-sided inverse of `diagonalSkewMatrix`. -/
def diagonalSkewMatrixInverse
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    DegreeEightAlgebra p q :=
  !![0, -1; z.inv, 0]

@[simp] theorem diagonalSkewMatrix_mul_inverse
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    diagonalSkewMatrix p q z * diagonalSkewMatrixInverse p q z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalSkewMatrix, diagonalSkewMatrixInverse,
      Matrix.mul_apply, Fin.sum_univ_two, z.val_mul_inv]

@[simp] theorem diagonalSkewMatrix_inverse_mul
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    diagonalSkewMatrixInverse p q z * diagonalSkewMatrix p q z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalSkewMatrix, diagonalSkewMatrixInverse,
      Matrix.mul_apply, Fin.sum_univ_two, z.inv_mul_val]

/-- The intrinsic antidiagonal witness is skew-adjoint for the involution
attached to `diag(1,z)`. -/
theorem diagonalDegreeEightAdjoint_skewMatrix
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    (diagonalDegreeEightGram p q z).adjoint
        (diagonalSkewMatrix p q z) =
      -diagonalSkewMatrix p q z := by
  apply (diagonalDegreeEightAdjoint_eq_neg_iff p q z
    (diagonalSkewMatrix p q z)).2
  simp [diagonalSkewMatrix, z.star_val, z.inv_mul_val]

/-- The antidiagonal witness bundled as an invertible skew-adjoint element of
the actual degree-eight adjoint algebra. -/
noncomputable def diagonalAdjointSkewUnit
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    SkewAdjointUnit (A := DiagonalDegreeEightAdjointAlgebra p q z) where
  val := ⟨diagonalSkewMatrix p q z⟩
  inv := ⟨diagonalSkewMatrixInverse p q z⟩
  val_mul_inv := by
    apply AdjointAlgebra.ext
    change diagonalSkewMatrix p q z * diagonalSkewMatrixInverse p q z = 1
    exact diagonalSkewMatrix_mul_inverse p q z
  inv_mul_val := by
    apply AdjointAlgebra.ext
    change diagonalSkewMatrixInverse p q z * diagonalSkewMatrix p q z = 1
    exact diagonalSkewMatrix_inverse_mul p q z
  star_val := by
    apply AdjointAlgebra.ext
    change (diagonalDegreeEightGram p q z).adjoint
      (diagonalSkewMatrix p q z) = -diagonalSkewMatrix p q z
    exact diagonalDegreeEightAdjoint_skewMatrix p q z

end RiemannResearch.E7.QuaternionHermitian
