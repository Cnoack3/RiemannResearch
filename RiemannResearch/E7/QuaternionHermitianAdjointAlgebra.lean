/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianGram
import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.Algebra.Ring.TransferInstance

/-!
# The adjoint algebra attached to a hermitian Gram datum

For an invertible hermitian Gram matrix `G`, `AdjointAlgebra G` packages the
matrix ring with involution `X ↦ G⁻¹ X⋆ G`.  The involution is verified to be
additive, anti-multiplicative, involutive, semilinear over the base star, and
of the first kind when the base star is trivial.

In the rank-two biquaternion specialization the algebra has verified dimension
`64`, hence degree eight over a field.  This is not yet a quadratic pair: no
orthogonal-type, semitrace, or Clifford-component theorem is assumed here.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u v w

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {A : Type v} [Ring A] [StarRing A]

/-- The matrix algebra equipped with the adjoint involution attached to `G`. -/
structure AdjointAlgebra (G : HermitianGram (ι := ι) (A := A)) where
  val : Matrix ι ι A

namespace AdjointAlgebra

variable (G : HermitianGram (ι := ι) (A := A))

/-- Forget the chosen adjoint involution. -/
def equiv : AdjointAlgebra G ≃ Matrix ι ι A where
  toFun := val
  invFun := mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

instance instRing : Ring (AdjointAlgebra G) := (equiv G).ring

@[simp] theorem val_zero : (0 : AdjointAlgebra G).val = 0 := rfl
@[simp] theorem val_one : (1 : AdjointAlgebra G).val = 1 := rfl
@[simp] theorem val_add (x y : AdjointAlgebra G) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_mul (x y : AdjointAlgebra G) : (x * y).val = x.val * y.val := rfl
@[simp] theorem val_neg (x : AdjointAlgebra G) : (-x).val = -x.val := rfl

@[ext] theorem ext {x y : AdjointAlgebra G} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- The underlying ring is canonically the matrix ring. -/
def ringEquiv : AdjointAlgebra G ≃+* Matrix ι ι A where
  toEquiv := equiv G
  map_add' := val_add G
  map_mul' := val_mul G

instance instStar : Star (AdjointAlgebra G) where
  star x := ⟨G.adjoint x.val⟩

@[simp] theorem val_star (x : AdjointAlgebra G) :
    (star x).val = G.adjoint x.val := rfl

instance instStarRing : StarRing (AdjointAlgebra G) where
  star_involutive x := by
    apply ext
    exact G.adjoint_involutive x.val
  star_mul x y := by
    apply ext
    exact G.adjoint_mul x.val y.val
  star_add x y := by
    apply ext
    exact G.adjoint_add x.val y.val

section Algebra

variable {R : Type w} [CommSemiring R] [Algebra R A]

instance instAlgebra : Algebra R (AdjointAlgebra G) :=
  Equiv.algebra R (equiv G)

/-- Forgetting the involution gives an algebra equivalence with matrices. -/
def algEquiv : AdjointAlgebra G ≃ₐ[R] Matrix ι ι A :=
  Equiv.algEquiv R (equiv G)

@[simp] theorem algEquiv_apply (x : AdjointAlgebra G) :
    algEquiv (G := G) (R := R) x = x.val := rfl

@[simp] theorem val_smul (r : R) (x : AdjointAlgebra G) :
    (r • x).val = r • x.val := by
  change algEquiv (G := G) (R := R) (r • x) =
    r • algEquiv (G := G) (R := R) x
  exact map_smul (algEquiv (G := G) (R := R)) r x

@[simp] theorem val_algebraMap (r : R) :
    (algebraMap R (AdjointAlgebra G) r).val =
      algebraMap R (Matrix ι ι A) r := by
  change algEquiv (G := G) (R := R)
      (algebraMap R (AdjointAlgebra G) r) =
    algebraMap R (Matrix ι ι A) r
  exact (algEquiv (G := G) (R := R)).commutes r

end Algebra

section StarModule

variable {R : Type w} [CommRing R] [StarRing R]
variable [Algebra R A] [StarModule R A]

/-- The adjoint involution is semilinear over the base star. -/
lemma adjoint_smul (r : R) (X : Matrix ι ι A) :
    G.adjoint (r • X) = star r • G.adjoint X := by
  simp only [HermitianGram.adjoint, StarModule.star_smul]
  rw [Algebra.mul_smul_comm]
  rw [smul_mul_assoc]

instance instStarModule : StarModule R (AdjointAlgebra G) where
  star_smul r x := by
    apply ext
    rw [val_star, val_smul, val_smul, val_star]
    exact adjoint_smul G r x.val

@[simp] theorem star_algebraMap (r : R) :
    star (algebraMap R (AdjointAlgebra G) r) =
      algebraMap R (AdjointAlgebra G) (star r) := by
  calc
    star (algebraMap R (AdjointAlgebra G) r) =
        star (r • (1 : AdjointAlgebra G)) := by
      simp [Algebra.smul_def]
    _ = star r • star (1 : AdjointAlgebra G) := StarModule.star_smul r 1
    _ = algebraMap R (AdjointAlgebra G) (star r) := by
      simp [Algebra.smul_def]

end StarModule

section FirstKind

variable {R : Type w} [CommRing R] [StarRing R] [TrivialStar R]
variable [Algebra R A] [StarModule R A]

/-- Over a trivially starred base, the adjoint involution fixes every scalar. -/
@[simp] theorem star_algebraMap_of_trivial (r : R) :
    star (algebraMap R (AdjointAlgebra G) r) =
      algebraMap R (AdjointAlgebra G) r := by
  rw [star_algebraMap]
  rw [TrivialStar.star_trivial]

end FirstKind

end AdjointAlgebra

section DegreeEight

variable {k : Type u} [CommRing k] [StarRing k] [TrivialStar k]

/-- The rank-two biquaternion adjoint algebra. -/
abbrev DegreeEightAdjointAlgebra
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q) :=
  AdjointAlgebra G

/-- The adjoint algebra attached to the diagonal Gram matrix `diag(1,z)`. -/
abbrev DiagonalDegreeEightAdjointAlgebra
    (p q : QuaternionParameters k)
    (z : SelfAdjointUnit (A := Biquaternion p q)) :=
  DegreeEightAdjointAlgebra p q (diagonalDegreeEightGram p q z)

/-- The adjoint algebra attached to `diag(1,j⊗j')`. -/
abbrev JTensorDegreeEightAdjointAlgebra
    (p q : QuaternionParameters k) (hp : JUnitData p) (hq : JUnitData q) :=
  DegreeEightAdjointAlgebra p q (jTensorDegreeEightGram p q hp hq)

end DegreeEight

section DegreeEightDimension

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]

@[simp] theorem degreeEightAdjointAlgebra_finrank
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q) :
    Module.finrank k (DegreeEightAdjointAlgebra p q G) = 64 := by
  calc
    Module.finrank k (DegreeEightAdjointAlgebra p q G) =
        Module.finrank k (DegreeEightAlgebra p q) :=
      (AdjointAlgebra.algEquiv (G := G) (R := k)).toLinearEquiv.finrank_eq
    _ = 64 := degreeEightAlgebra_finrank p q

end DegreeEightDimension

end RiemannResearch.E7.QuaternionHermitian
