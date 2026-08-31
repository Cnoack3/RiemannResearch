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

This isolates the remaining E7 realization problem: choose `z` so that the
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

end RiemannResearch.E7.QuaternionHermitian
