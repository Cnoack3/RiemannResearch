/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianDegreeEight
import Mathlib.Tactic.FinCases

/-!
# Explicit hermitian Gram data for the degree-eight E7 boundary

This file turns the quaternion and biquaternion algebras from
`QuaternionHermitianDegreeEight` into nontrivial rank-two hermitian data.

The principal construction is

`diagonalDegreeEightGram p q z = diag(1,z)`,

where `z` is an invertible self-adjoint element of the biquaternion algebra
`PresentedQuaternion p ⊗ PresentedQuaternion q`.  It therefore exposes the
remaining object-level parameter in the hermitian attack on the E7
index-eight boundary.

The file also constructs a concrete such coefficient from the standard
skew-adjoint generators: if both `j²` scalars are units, then `j ⊗ j'` is an
invertible self-adjoint biquaternion element.

No Clifford-component calculation is asserted here.  The remaining E7 bridge
still requires choosing a self-adjoint coefficient whose adjoint involution
has the prescribed two Clifford classes.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u v w

section Units

variable {A : Type u} [Ring A] [StarRing A]

/-- A chosen two-sided inverse for an element. -/
structure TwoSidedUnit where
  val : A
  inv : A
  val_mul_inv : val * inv = 1
  inv_mul_val : inv * val = 1

/-- An invertible self-adjoint element. -/
structure SelfAdjointUnit extends TwoSidedUnit (A := A) where
  star_val : star val = val

/-- An invertible skew-adjoint element. -/
structure SkewAdjointUnit extends TwoSidedUnit (A := A) where
  star_val : star val = -val

namespace SelfAdjointUnit

@[simp] theorem star_inv (x : SelfAdjointUnit (A := A)) :
    star x.inv = x.inv := by
  have h : star x.inv * x.val = 1 := by
    calc
      star x.inv * x.val = star x.inv * star x.val := by rw [x.star_val]
      _ = star (x.val * x.inv) := (StarMul.star_mul _ _).symm
      _ = 1 := by rw [x.val_mul_inv, star_one]
  calc
    star x.inv = star x.inv * 1 := by simp
    _ = star x.inv * (x.val * x.inv) := by rw [x.val_mul_inv]
    _ = (star x.inv * x.val) * x.inv := by rw [mul_assoc]
    _ = x.inv := by rw [h]; simp

/-- The unit element as an invertible self-adjoint element. -/
@[simp] def one : SelfAdjointUnit (A := A) where
  val := 1
  inv := 1
  val_mul_inv := by simp
  inv_mul_val := by simp
  star_val := star_one A

end SelfAdjointUnit

end Units

section Tensor

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]
variable {A : Type v} [Ring A] [Algebra R A] [StarRing A] [StarModule R A]
variable {B : Type w} [Ring B] [Algebra R B] [StarRing B] [StarModule R B]

namespace SkewAdjointUnit

/-- The tensor of two skew-adjoint units is a self-adjoint unit. -/
noncomputable def tensor
    (x : SkewAdjointUnit (A := A)) (y : SkewAdjointUnit (A := B)) :
    SelfAdjointUnit (A := TensorProduct R A B) where
  val := x.val ⊗ₜ[R] y.val
  inv := x.inv ⊗ₜ[R] y.inv
  val_mul_inv := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, x.val_mul_inv, y.val_mul_inv]
    exact Algebra.TensorProduct.one_def.symm
  inv_mul_val := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, x.inv_mul_val, y.inv_mul_val]
    exact Algebra.TensorProduct.one_def.symm
  star_val := by
    rw [TensorProduct.star_tmul, x.star_val, y.star_val]
    calc
      (-x.val) ⊗ₜ[R] (-y.val) = -(x.val ⊗ₜ[R] (-y.val)) :=
        TensorProduct.neg_tmul x.val (-y.val)
      _ = -(-(x.val ⊗ₜ[R] y.val)) := by rw [TensorProduct.tmul_neg]
      _ = x.val ⊗ₜ[R] y.val := neg_neg _

end SkewAdjointUnit

end Tensor

section QuaternionJ

variable {k : Type u} [CommRing k]

/-- Explicit inverse data for the scalar `c₃ = j²`. -/
structure JUnitData (p : QuaternionParameters k) where
  inverse : k
  c₃_mul_inverse : p.c₃ * inverse = 1
  inverse_mul_c₃ : inverse * p.c₃ = 1

namespace JUnitData

/-- Extract `j²` inverse data from an `IsUnit` proof. -/
noncomputable def ofIsUnit (p : QuaternionParameters k) (h : IsUnit p.c₃) :
    JUnitData p where
  inverse := ↑(h.unit)⁻¹
  c₃_mul_inverse := by
    calc
      p.c₃ * ↑(h.unit)⁻¹ = (↑h.unit : k) * ↑(h.unit)⁻¹ := by
        exact congrArg (fun z : k => z * ↑(h.unit)⁻¹) h.unit_spec.symm
      _ = 1 := Units.mul_inv h.unit
  inverse_mul_c₃ := by
    calc
      ↑(h.unit)⁻¹ * p.c₃ = ↑(h.unit)⁻¹ * (↑h.unit : k) := by
        exact congrArg (fun z : k => ↑(h.unit)⁻¹ * z) h.unit_spec.symm
      _ = 1 := Units.inv_mul h.unit

end JUnitData

namespace PresentedQuaternion

/-- The generator `j`, as an invertible skew-adjoint element when `j²` is a unit. -/
noncomputable def jSkewAdjointUnit
    (p : QuaternionParameters k) (h : JUnitData p) :
    SkewAdjointUnit (A := PresentedQuaternion p) where
  val := j p
  inv := h.inverse • j p
  val_mul_inv := by
    rw [Algebra.mul_smul_comm]
    rw [j_mul_j]
    rw [Algebra.smul_def, ← map_mul]
    rw [mul_comm h.inverse p.c₃, h.c₃_mul_inverse, map_one]
  inv_mul_val := by
    rw [smul_mul_assoc]
    rw [j_mul_j]
    rw [Algebra.smul_def, ← map_mul, h.inverse_mul_c₃, map_one]
  star_val := star_j p

/-- The `j` skew unit obtained directly from an `IsUnit` proof for `j²`. -/
noncomputable def jSkewAdjointUnitOfIsUnit
    (p : QuaternionParameters k) (h : IsUnit p.c₃) :
    SkewAdjointUnit (A := PresentedQuaternion p) :=
  jSkewAdjointUnit p (JUnitData.ofIsUnit p h)

end PresentedQuaternion

end QuaternionJ

section Matrix

variable {A : Type u} [Ring A] [StarRing A]

namespace HermitianGram

/-- The diagonal rank-two hermitian Gram matrix with self-adjoint unit entries. -/
noncomputable def diagonalTwo
    (x y : SelfAdjointUnit (A := A)) :
    HermitianGram (ι := Fin 2) (A := A) where
  matrix := Matrix.diagonal ![x.val, y.val]
  inverse := Matrix.diagonal ![x.inv, y.inv]
  matrix_mul_inverse := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [x.val_mul_inv, y.val_mul_inv]
  inverse_mul_matrix := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [x.inv_mul_val, y.inv_mul_val]
  star_matrix := by
    change (Matrix.diagonal ![x.val, y.val]).conjTranspose =
      Matrix.diagonal ![x.val, y.val]
    rw [Matrix.diagonal_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [x.star_val, y.star_val]

@[simp] theorem diagonalTwo_matrix (x y : SelfAdjointUnit (A := A)) :
    (diagonalTwo x y).matrix = Matrix.diagonal ![x.val, y.val] := rfl

@[simp] theorem diagonalTwo_inverse (x y : SelfAdjointUnit (A := A)) :
    (diagonalTwo x y).inverse = Matrix.diagonal ![x.inv, y.inv] := rfl

end HermitianGram

end Matrix

section DegreeEight

variable {k : Type u} [CommRing k] [StarRing k] [TrivialStar k]

/-- A concrete self-adjoint biquaternion unit obtained from the two `j` generators. -/
noncomputable def jTensorSelfAdjointUnit
    (p q : QuaternionParameters k) (hp : JUnitData p) (hq : JUnitData q) :
    SelfAdjointUnit (A := Biquaternion p q) :=
  SkewAdjointUnit.tensor
    (PresentedQuaternion.jSkewAdjointUnit p hp)
    (PresentedQuaternion.jSkewAdjointUnit q hq)

/-- The degree-eight diagonal Gram datum `diag(1,z)`. -/
noncomputable def diagonalDegreeEightGram
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    DegreeEightHermitianGram p q :=
  HermitianGram.diagonalTwo SelfAdjointUnit.one z

/-- The explicit degree-eight Gram datum `diag(1,j⊗j')`. -/
noncomputable def jTensorDegreeEightGram
    (p q : QuaternionParameters k) (hp : JUnitData p) (hq : JUnitData q) :
    DegreeEightHermitianGram p q :=
  diagonalDegreeEightGram p q (jTensorSelfAdjointUnit p q hp hq)

@[simp] theorem diagonalDegreeEightGram_matrix
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :
    (diagonalDegreeEightGram p q z).matrix = Matrix.diagonal ![1, z.val] := by
  rfl

@[simp] theorem jTensorDegreeEightGram_matrix
    (p q : QuaternionParameters k) (hp : JUnitData p) (hq : JUnitData q) :
    (jTensorDegreeEightGram p q hp hq).matrix =
      Matrix.diagonal ![1, PresentedQuaternion.j p ⊗ₜ[k] PresentedQuaternion.j q] := by
  rfl

end DegreeEight

end RiemannResearch.E7.QuaternionHermitian
