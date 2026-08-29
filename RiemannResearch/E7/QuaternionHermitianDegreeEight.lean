/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Star.TensorProduct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quaternion and hermitian foundations for the degree-eight E7 boundary

The remaining E7 bridge asks for an actual degree-eight algebra with quadratic
pair, not merely a balanced triple of Brauer classes.  This file starts the
object-level side of that construction.

It supplies:

* Mathlib's uniform three-parameter quaternion presentation, covering both
  ordinary symbol algebras and characteristic-two quaternion presentations;
* the standard generators and their defining relations;
* the reduced norm and its multiplicativity;
* the canonical tensor involution on a biquaternion algebra;
* the algebra `M₂(Q ⊗ Q')`, with verified dimension `64` over a field;
* the adjoint involution associated with an arbitrary invertible hermitian
  Gram matrix.

This is genuine algebraic infrastructure, but it does **not** yet calculate
the Clifford components of the adjoint involution.  That calculation is the
next object-level step needed to connect this module to
`IndexEightCentralTargetEffectivityGoal`.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u v

/-- Parameters for Mathlib's uniform quaternion presentation. -/
structure QuaternionParameters (k : Type u) where
  c₁ : k
  c₂ : k
  c₃ : k

section Presented

variable {k : Type u} [CommRing k]

/-- The quaternion algebra with relations `i² = c₁ + c₂ i`, `j² = c₃`. -/
abbrev PresentedQuaternion (p : QuaternionParameters k) :=
  QuaternionAlgebra k p.c₁ p.c₂ p.c₃

/-- The usual symbol presentation in characteristic different from two. -/
def symbolParameters (a b : k) : QuaternionParameters k :=
  ⟨a, 0, b⟩

/-- The usual `[a,b)` presentation in characteristic two. -/
def characteristicTwoParameters (a b : k) : QuaternionParameters k :=
  ⟨a, 1, b⟩

/-- The characteristic-different-from-two symbol algebra `(a,b)`. -/
abbrev SymbolQuaternion (a b : k) :=
  PresentedQuaternion (symbolParameters a b)

/-- The characteristic-two quaternion presentation `[a,b)`. -/
abbrev CharacteristicTwoQuaternion (a b : k) :=
  PresentedQuaternion (characteristicTwoParameters a b)

namespace PresentedQuaternion

variable (p : QuaternionParameters k)

/-- The standard quaternion generator `i`. -/
def i : PresentedQuaternion p := QuaternionAlgebra.mk 0 1 0 0

/-- The standard quaternion generator `j`. -/
def j : PresentedQuaternion p := QuaternionAlgebra.mk 0 0 1 0

/-- The standard product generator `k = i j`. -/
def kBasis : PresentedQuaternion p := QuaternionAlgebra.mk 0 0 0 1

@[simp] theorem i_mul_i :
    i p * i p = algebraMap k (PresentedQuaternion p) p.c₁ + p.c₂ • i p := by
  ext <;> simp [i, PresentedQuaternion, QuaternionAlgebra.algebraMap_eq]

@[simp] theorem j_mul_j :
    j p * j p = algebraMap k (PresentedQuaternion p) p.c₃ := by
  ext <;> simp [j, PresentedQuaternion, QuaternionAlgebra.algebraMap_eq]

@[simp] theorem i_mul_j : i p * j p = kBasis p := by
  ext <;> simp [i, j, kBasis, PresentedQuaternion]

@[simp] theorem j_mul_i : j p * i p = p.c₂ • j p - kBasis p := by
  ext <;> simp [i, j, kBasis, PresentedQuaternion]

@[simp] theorem star_i :
    star (i p) = algebraMap k (PresentedQuaternion p) p.c₂ - i p := by
  ext <;> simp [i, PresentedQuaternion, QuaternionAlgebra.algebraMap_eq]

@[simp] theorem star_j : star (j p) = -j p := by
  ext <;> simp [j, PresentedQuaternion]

@[simp] theorem star_kBasis : star (kBasis p) = -kBasis p := by
  ext <;> simp [kBasis, PresentedQuaternion]

/-- The reduced norm in the uniform three-parameter presentation. -/
def reducedNorm (x : PresentedQuaternion p) : k :=
  x.re * x.re + p.c₂ * x.re * x.imI - p.c₁ * x.imI * x.imI -
    p.c₃ * x.imJ * x.imJ - p.c₂ * p.c₃ * x.imJ * x.imK +
      p.c₁ * p.c₃ * x.imK * x.imK

@[simp] theorem mul_star (x : PresentedQuaternion p) :
    x * star x = algebraMap k (PresentedQuaternion p) (reducedNorm p x) := by
  rw [QuaternionAlgebra.algebraMap_eq]
  ext <;> simp [reducedNorm] <;> ring

@[simp] theorem star_mul (x : PresentedQuaternion p) :
    star x * x = algebraMap k (PresentedQuaternion p) (reducedNorm p x) := by
  rw [QuaternionAlgebra.algebraMap_eq]
  ext <;> simp [reducedNorm] <;> ring

@[simp] theorem reducedNorm_one : reducedNorm p 1 = 1 := by
  simp [reducedNorm]

@[simp] theorem reducedNorm_mul (x y : PresentedQuaternion p) :
    reducedNorm p (x * y) = reducedNorm p x * reducedNorm p y := by
  simp [reducedNorm]
  ring

/-- The reduced norm as a multiplicative map. -/
def reducedNormHom : PresentedQuaternion p →* k where
  toFun := reducedNorm p
  map_one' := reducedNorm_one p
  map_mul' := reducedNorm_mul p

end PresentedQuaternion
end Presented

section StarModule

variable {k : Type u} [CommRing k] [StarRing k] [TrivialStar k]

/-- Canonical quaternion conjugation is linear over a trivially starred base. -/
instance presentedQuaternionStarModule (p : QuaternionParameters k) :
    StarModule k (PresentedQuaternion p) where
  star_smul r x := by
    calc
      star (r • x) = r • star x := QuaternionAlgebra.star_smul r x
      _ = star r • star x := by rw [TrivialStar.star_trivial r]

end StarModule

section Biquaternion

variable {k : Type u} [CommRing k]

/-- Tensor product of two presented quaternion algebras. -/
abbrev Biquaternion (p q : QuaternionParameters k) :=
  TensorProduct k (PresentedQuaternion p) (PresentedQuaternion q)

/-- The matrix algebra `M₂(Q ⊗ Q')`; over a field it has degree eight. -/
abbrev DegreeEightAlgebra (p q : QuaternionParameters k) :=
  Matrix (Fin 2) (Fin 2) (Biquaternion p q)

end Biquaternion

section BiquaternionStar

variable {k : Type u} [CommRing k] [StarRing k] [TrivialStar k]

@[simp] theorem star_tmul
    {p q : QuaternionParameters k}
    (x : PresentedQuaternion p) (y : PresentedQuaternion q) :
    star (x ⊗ₜ[k] y) = star x ⊗ₜ[k] star y := by
  exact TensorProduct.star_tmul x y

end BiquaternionStar

section Dimension

variable {k : Type u} [Field k]

@[simp] theorem presentedQuaternion_finrank (p : QuaternionParameters k) :
    Module.finrank k (PresentedQuaternion p) = 4 := by
  exact QuaternionAlgebra.finrank_eq_four p.c₁ p.c₂ p.c₃

@[simp] theorem biquaternion_finrank (p q : QuaternionParameters k) :
    Module.finrank k (Biquaternion p q) = 16 := by
  rw [Module.finrank_tensorProduct]
  rw [presentedQuaternion_finrank, presentedQuaternion_finrank]

@[simp] theorem degreeEightAlgebra_finrank (p q : QuaternionParameters k) :
    Module.finrank k (DegreeEightAlgebra p q) = 64 := by
  change Module.finrank k (Fin 2 → Fin 2 → Biquaternion p q) = 64
  rw [Module.finrank_pi_fintype]
  simp only [Fin.sum_univ_two]
  simp only [Module.finrank_pi_fintype, Fin.sum_univ_two,
    biquaternion_finrank]
  norm_num

end Dimension

section HermitianAdjoint

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {A : Type v} [Ring A] [StarRing A]

/-- An invertible hermitian Gram matrix, including a chosen two-sided inverse. -/
structure HermitianGram where
  matrix : Matrix ι ι A
  inverse : Matrix ι ι A
  matrix_mul_inverse : matrix * inverse = 1
  inverse_mul_matrix : inverse * matrix = 1
  star_matrix : star matrix = matrix

namespace HermitianGram

variable (G : HermitianGram (ι := ι) (A := A))

@[simp] theorem star_inverse : star G.inverse = G.inverse := by
  have h : star G.inverse * G.matrix = 1 := by
    rw [← G.star_matrix, ← StarMul.star_mul, G.matrix_mul_inverse]
    simp
  calc
    star G.inverse = star G.inverse * 1 := by simp
    _ = star G.inverse * (G.matrix * G.inverse) := by rw [G.matrix_mul_inverse]
    _ = (star G.inverse * G.matrix) * G.inverse := by rw [mul_assoc]
    _ = G.inverse := by rw [h]; simp

/-- The adjoint involution associated with the Gram matrix. -/
def adjoint (X : Matrix ι ι A) : Matrix ι ι A :=
  G.inverse * star X * G.matrix

@[simp] theorem adjoint_zero : G.adjoint 0 = 0 := by
  simp [adjoint]

@[simp] theorem adjoint_add (X Y : Matrix ι ι A) :
    G.adjoint (X + Y) = G.adjoint X + G.adjoint Y := by
  simp [adjoint, mul_add, add_mul]

@[simp] theorem adjoint_neg (X : Matrix ι ι A) :
    G.adjoint (-X) = -G.adjoint X := by
  simp [adjoint]

@[simp] theorem adjoint_one : G.adjoint 1 = 1 := by
  simp [adjoint, G.inverse_mul_matrix]

@[simp] theorem adjoint_mul (X Y : Matrix ι ι A) :
    G.adjoint (X * Y) = G.adjoint Y * G.adjoint X := by
  change G.inverse * star (X * Y) * G.matrix =
    (G.inverse * star Y * G.matrix) * (G.inverse * star X * G.matrix)
  rw [StarMul.star_mul]
  calc
    G.inverse * (star Y * star X) * G.matrix =
        G.inverse * star Y * star X * G.matrix := by simp only [mul_assoc]
    _ = G.inverse * star Y * 1 * star X * G.matrix := by simp
    _ = G.inverse * star Y * (G.matrix * G.inverse) * star X * G.matrix := by
      rw [G.matrix_mul_inverse]
    _ = (G.inverse * star Y * G.matrix) *
        (G.inverse * star X * G.matrix) := by simp only [mul_assoc]

@[simp] theorem adjoint_involutive : Function.Involutive G.adjoint := by
  intro X
  simp only [adjoint, StarMul.star_mul, G.star_matrix, G.star_inverse, star_star]
  calc
    G.inverse * (G.matrix * (X * G.inverse)) * G.matrix =
        ((G.inverse * G.matrix) * (X * G.inverse)) * G.matrix := by
          simp only [mul_assoc]
    _ = (X * G.inverse) * G.matrix := by rw [G.inverse_mul_matrix, one_mul]
    _ = X * (G.inverse * G.matrix) := by rw [mul_assoc]
    _ = X := by rw [G.inverse_mul_matrix, mul_one]

/-- The unit Gram matrix. -/
def standard : HermitianGram (ι := ι) (A := A) where
  matrix := 1
  inverse := 1
  matrix_mul_inverse := by simp
  inverse_mul_matrix := by simp
  star_matrix := by simp

@[simp] theorem standard_adjoint (X : Matrix ι ι A) :
    (standard (ι := ι) (A := A)).adjoint X = star X := by
  simp [standard, adjoint]

end HermitianGram
end HermitianAdjoint

section DegreeEightHermitian

variable {k : Type u} [CommRing k] [StarRing k] [TrivialStar k]

/-- A rank-two hermitian Gram datum on a biquaternion algebra. -/
abbrev DegreeEightHermitianGram (p q : QuaternionParameters k) :=
  HermitianGram (ι := Fin 2) (A := Biquaternion p q)

/-- The standard rank-two hermitian datum. -/
noncomputable def standardDegreeEightHermitianGram (p q : QuaternionParameters k) :
    DegreeEightHermitianGram p q :=
  HermitianGram.standard

end DegreeEightHermitian

end RiemannResearch.E7.QuaternionHermitian
