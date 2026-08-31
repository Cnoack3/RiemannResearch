/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianSymmetricDimension
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic.FinCases

/-!
# Eigen-coordinates for canonical biquaternion conjugation

For a quaternion in Mathlib's uniform three-parameter presentation, the first
coordinate `2 * re + c₂ * imI` is fixed by canonical conjugation and the three
remaining coordinates are negated. Tensoring these bases diagonalizes the
canonical involution on a biquaternion algebra.

The fixed coordinates are exactly

* the scalar-scalar coordinate, and
* the nine imaginary-imaginary coordinates.

The mixed scalar-imaginary coordinates vanish on every self-adjoint
biquaternion. This is the coordinate calculation needed to prove that the
self-adjoint subspace has dimension ten away from characteristic two.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u

section QuaternionCoordinates

variable {k : Type u} [Field k]

/-- Coordinates in which quaternion conjugation has eigenvalues
`(1,-1,-1,-1)`. -/
noncomputable def quaternionEigenCoordinates
    (p : QuaternionParameters k) [NeZero (2 : k)] :
    PresentedQuaternion p ≃ₗ[k] (Fin 4 → k) where
  toFun x := ![2 * x.re + p.c₂ * x.imI, x.imI, x.imJ, x.imK]
  invFun f := QuaternionAlgebra.mk
    ((2 : k)⁻¹ * (f 0 - p.c₂ * f 1)) (f 1) (f 2) (f 3)
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp <;> ring
  left_inv x := by
    ext
    · simp
      field_simp
    · simp
    · simp
    · simp
  right_inv f := by
    ext i
    fin_cases i
    · simp
      field_simp
      ring
    · simp
    · simp
    · simp

/-- The basis corresponding to `quaternionEigenCoordinates`. -/
noncomputable def quaternionEigenBasis
    (p : QuaternionParameters k) [NeZero (2 : k)] :
    Module.Basis (Fin 4) k (PresentedQuaternion p) :=
  Module.Basis.ofEquivFun (quaternionEigenCoordinates p)

/-- The tensor-product eigenbasis on a biquaternion algebra. -/
noncomputable def biquaternionEigenBasis
    (p q : QuaternionParameters k) [NeZero (2 : k)] :
    Module.Basis (Fin 4 × Fin 4) k (Biquaternion p q) :=
  (quaternionEigenBasis p).tensorProduct (quaternionEigenBasis q)

/-- Eigenvalue of quaternion conjugation at an eigen-coordinate. -/
noncomputable def quaternionEigenSign (i : Fin 4) : k :=
  if i = 0 then 1 else -1

@[simp] theorem quaternionEigenCoordinates_star
    (p : QuaternionParameters k) [NeZero (2 : k)]
    (x : PresentedQuaternion p) (i : Fin 4) :
    quaternionEigenCoordinates p (star x) i =
      quaternionEigenSign i * quaternionEigenCoordinates p x i := by
  fin_cases i <;>
    simp [quaternionEigenCoordinates, quaternionEigenSign] <;>
    ring

@[simp] theorem biquaternionEigenCoordinates_tmul
    (p q : QuaternionParameters k) [NeZero (2 : k)]
    (x : PresentedQuaternion p) (y : PresentedQuaternion q)
    (i j : Fin 4) :
    (biquaternionEigenBasis p q).equivFun (x ⊗ₜ[k] y) (i, j) =
      quaternionEigenCoordinates p x i *
        quaternionEigenCoordinates q y j := by
  rw [Module.Basis.equivFun_apply]
  unfold biquaternionEigenBasis
  rw [Module.Basis.tensorProduct_repr_tmul_apply]
  change quaternionEigenCoordinates q y j *
      quaternionEigenCoordinates p x i = _
  ring

end QuaternionCoordinates

section TensorStar

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]

@[simp] theorem biquaternionEigenCoordinates_star
    (p q : QuaternionParameters k) [NeZero (2 : k)]
    (z : Biquaternion p q) (ij : Fin 4 × Fin 4) :
    (biquaternionEigenBasis p q).equivFun (star z) ij =
      (quaternionEigenSign ij.1 * quaternionEigenSign ij.2) *
        (biquaternionEigenBasis p q).equivFun z ij := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [star_add, map_add, Pi.add_apply]
      rw [hx, hy, mul_add]
  | tmul x y =>
      rcases ij with ⟨i, j⟩
      simp [mul_assoc, mul_left_comm]

private lemma eq_zero_of_neg_eq_self_of_two_ne_zero
    [NeZero (2 : k)] {a : k} (h : -a = a) : a = 0 := by
  have hsum : a + a = 0 := by
    have hh := congrArg (fun z : k => z + a) h
    simpa using hh.symm
  have h2 : (2 : k) * a = 0 := by
    simpa [two_mul] using hsum
  exact (mul_eq_zero.mp h2).resolve_left (NeZero.ne (2 : k))

@[simp] theorem biquaternionEigenCoordinate_zero_succ_of_symmetric
    (p q : QuaternionParameters k) [NeZero (2 : k)]
    (z : symmetricSubmodule (k := k) (A := Biquaternion p q))
    (j : Fin 3) :
    (biquaternionEigenBasis p q).equivFun z.1 (0, j.succ) = 0 := by
  have hcoord := congrArg
    (fun w : Biquaternion p q =>
      (biquaternionEigenBasis p q).equivFun w (0, j.succ)) z.2
  rw [biquaternionEigenCoordinates_star] at hcoord
  simp [quaternionEigenSign] at hcoord
  exact eq_zero_of_neg_eq_self_of_two_ne_zero hcoord

@[simp] theorem biquaternionEigenCoordinate_succ_zero_of_symmetric
    (p q : QuaternionParameters k) [NeZero (2 : k)]
    (z : symmetricSubmodule (k := k) (A := Biquaternion p q))
    (i : Fin 3) :
    (biquaternionEigenBasis p q).equivFun z.1 (i.succ, 0) = 0 := by
  have hcoord := congrArg
    (fun w : Biquaternion p q =>
      (biquaternionEigenBasis p q).equivFun w (i.succ, 0)) z.2
  rw [biquaternionEigenCoordinates_star] at hcoord
  simp [quaternionEigenSign] at hcoord
  exact eq_zero_of_neg_eq_self_of_two_ne_zero hcoord

end TensorStar

section SymmetricCoordinateIndex

/-- One scalar-scalar coordinate and nine imaginary-imaginary coordinates. -/
abbrev BiquaternionSymmetricCoordinateIndex :=
  Unit ⊕ (Fin 3 × Fin 3)

/-- Inclusion of the ten symmetric coordinate indices into all sixteen tensor
coordinate indices. -/
def symmetricCoordinatePair :
    BiquaternionSymmetricCoordinateIndex → Fin 4 × Fin 4
  | Sum.inl _ => (0, 0)
  | Sum.inr ij => (ij.1.succ, ij.2.succ)

/-- Extend ten symmetric coordinates by zero on the six mixed coordinates. -/
def extendSymmetricCoordinates {k : Type*} [Zero k]
    (f : BiquaternionSymmetricCoordinateIndex → k) :
    Fin 4 × Fin 4 → k := fun ij =>
  Fin.cases
    (Fin.cases (f (Sum.inl ())) (fun _ => 0) ij.2)
    (fun i => Fin.cases 0 (fun j => f (Sum.inr (i, j))) ij.2)
    ij.1

@[simp] theorem extendSymmetricCoordinates_zero_zero
    {k : Type*} [Zero k]
    (f : BiquaternionSymmetricCoordinateIndex → k) :
    extendSymmetricCoordinates f (0, 0) = f (Sum.inl ()) := rfl

@[simp] theorem extendSymmetricCoordinates_zero_succ
    {k : Type*} [Zero k]
    (f : BiquaternionSymmetricCoordinateIndex → k) (j : Fin 3) :
    extendSymmetricCoordinates f (0, j.succ) = 0 := by
  simp [extendSymmetricCoordinates]

@[simp] theorem extendSymmetricCoordinates_succ_zero
    {k : Type*} [Zero k]
    (f : BiquaternionSymmetricCoordinateIndex → k) (i : Fin 3) :
    extendSymmetricCoordinates f (i.succ, 0) = 0 := by
  simp [extendSymmetricCoordinates]

@[simp] theorem extendSymmetricCoordinates_succ_succ
    {k : Type*} [Zero k]
    (f : BiquaternionSymmetricCoordinateIndex → k) (i j : Fin 3) :
    extendSymmetricCoordinates f (i.succ, j.succ) =
      f (Sum.inr (i, j)) := by
  simp [extendSymmetricCoordinates]

@[simp] theorem extend_at_symmetricCoordinatePair
    {k : Type*} [Zero k]
    (f : BiquaternionSymmetricCoordinateIndex → k)
    (a : BiquaternionSymmetricCoordinateIndex) :
    extendSymmetricCoordinates f (symmetricCoordinatePair a) = f a := by
  rcases a with (_ | ⟨i, j⟩) <;>
    simp [symmetricCoordinatePair]

end SymmetricCoordinateIndex


section SymmetricDimension

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]

/-- The self-adjoint subspace of a biquaternion algebra with canonical
conjugation is linearly equivalent to one scalar-scalar coordinate and nine
imaginary-imaginary coordinates. -/
noncomputable def biquaternionSymmetricCoordinatesEquiv
    (p q : QuaternionParameters k) [NeZero (2 : k)] :
    symmetricSubmodule (k := k) (A := Biquaternion p q) ≃ₗ[k]
      (BiquaternionSymmetricCoordinateIndex → k) where
  toFun z a :=
    (biquaternionEigenBasis p q).equivFun z.1
      (symmetricCoordinatePair a)
  invFun f := ⟨(biquaternionEigenBasis p q).equivFun.symm
      (extendSymmetricCoordinates f), by
    apply (biquaternionEigenBasis p q).equivFun.injective
    ext ij
    rw [biquaternionEigenCoordinates_star]
    simp only [LinearEquiv.apply_symm_apply]
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [quaternionEigenSign]
      · simp [quaternionEigenSign]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [quaternionEigenSign]
      · simp [quaternionEigenSign]⟩
  map_add' x y := by
    ext a
    simp
  map_smul' r x := by
    ext a
    simp
  left_inv z := by
    apply Subtype.ext
    apply (biquaternionEigenBasis p q).equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    ext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [symmetricCoordinatePair]
      · simpa using
          (biquaternionEigenCoordinate_zero_succ_of_symmetric p q z j).symm
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa using
          (biquaternionEigenCoordinate_succ_zero_of_symmetric p q z i).symm
      · simp [symmetricCoordinatePair]
  right_inv f := by
    ext a
    change (biquaternionEigenBasis p q).equivFun
      ((biquaternionEigenBasis p q).equivFun.symm
        (extendSymmetricCoordinates f)) (symmetricCoordinatePair a) = f a
    rw [LinearEquiv.apply_symm_apply]
    exact extend_at_symmetricCoordinatePair f a

/-- Canonical conjugation on a biquaternion algebra has a ten-dimensional
self-adjoint subspace when `2 ≠ 0`. -/
theorem biquaternionSymmetric_finrank
    (p q : QuaternionParameters k) [NeZero (2 : k)] :
    Module.finrank k
      (symmetricSubmodule (k := k) (A := Biquaternion p q)) = 10 := by
  calc
    _ = Module.finrank k (BiquaternionSymmetricCoordinateIndex → k) :=
      (biquaternionSymmetricCoordinatesEquiv p q).finrank_eq
    _ = Fintype.card BiquaternionSymmetricCoordinateIndex :=
      Module.finrank_pi k
    _ = 10 := by rfl

/-- The adjoint involution of a rank-two hermitian form over a biquaternion
algebra has the orthogonal fixed-space dimension `8 * 9 / 2 = 36`. -/
theorem degreeEightAdjointSymmetric_finrank
    (p q : QuaternionParameters k) [NeZero (2 : k)]
    (G : DegreeEightHermitianGram p q) :
    Module.finrank k
      (symmetricSubmodule
        (k := k) (A := DegreeEightAdjointAlgebra p q G)) = 36 := by
  rw [degreeEightAdjointSymmetric_finrank_formula p q G,
    biquaternionSymmetric_finrank, biquaternion_finrank]

end SymmetricDimension
end RiemannResearch.E7.QuaternionHermitian
