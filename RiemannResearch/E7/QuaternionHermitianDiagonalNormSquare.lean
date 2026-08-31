/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianGram

/-!
# The square norm term for the diagonal biquaternion coefficient

For the concrete hermitian Gram matrix `diag(1, j ⊗ j')`, this file proves the
exact quadratic relation

`(j ⊗ j')² = c₃c₃'`.

It also records the resulting square scalar `(c₃c₃')²`, which is the pure-
tensor reduced-norm term entering the usual discriminant formula for the
adjoint involution. We deliberately do not identify that scalar with a
formally defined reduced norm of the whole biquaternion algebra: that global
reduced-characteristic-polynomial layer is not yet present in the project.
Thus this is the concrete scalar calculation needed by the discriminant step,
not an assertion that the discriminant or Clifford components have already
been computed.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u

section QuaternionNorm

variable {k : Type u} [CommRing k]

/-- The standard skew generator has reduced norm `-c₃`. -/
@[simp] theorem PresentedQuaternion.reducedNorm_j
    (p : QuaternionParameters k) :
    PresentedQuaternion.reducedNorm p (PresentedQuaternion.j p) = -p.c₃ := by
  simp [PresentedQuaternion.reducedNorm, PresentedQuaternion.j]

/-- The standard pure-tensor reduced-norm expression for a tensor of two
quaternion elements. Both quaternion factors have degree two, hence both
reduced norms occur with exponent two. -/
def pureTensorReducedNormExpression
    (p q : QuaternionParameters k)
    (x : PresentedQuaternion p) (y : PresentedQuaternion q) : k :=
  (PresentedQuaternion.reducedNorm p x *
    PresentedQuaternion.reducedNorm q y) ^ 2

/-- For the diagonal coefficient `j ⊗ j'`, the pure-tensor norm expression is
the square `(c₃c₃')²`. -/
@[simp] theorem pureTensorReducedNormExpression_j_j
    (p q : QuaternionParameters k) :
    pureTensorReducedNormExpression p q
      (PresentedQuaternion.j p) (PresentedQuaternion.j q) =
      (p.c₃ * q.c₃) ^ 2 := by
  simp [pureTensorReducedNormExpression]

/-- The pure-tensor norm expression of `j ⊗ j'` has an explicit square
representative. -/
theorem pureTensorReducedNormExpression_j_j_isSquare
    (p q : QuaternionParameters k) :
    ∃ r : k,
      pureTensorReducedNormExpression p q
        (PresentedQuaternion.j p) (PresentedQuaternion.j q) = r ^ 2 := by
  exact ⟨p.c₃ * q.c₃, pureTensorReducedNormExpression_j_j p q⟩

/-- The tensor generator itself satisfies the scalar quadratic relation
`(j ⊗ j')² = c₃c₃'`. -/
@[simp] theorem jTensor_mul_self
    (p q : QuaternionParameters k) :
    (PresentedQuaternion.j p ⊗ₜ[k] PresentedQuaternion.j q) *
        (PresentedQuaternion.j p ⊗ₜ[k] PresentedQuaternion.j q) =
      algebraMap k (Biquaternion p q) (p.c₃ * q.c₃) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  simp only [PresentedQuaternion.j_mul_j]
  simp only [Algebra.TensorProduct.algebraMap_apply]
  simp only [Algebra.algebraMap_eq_smul_one]
  rw [TensorProduct.tmul_smul]
  rw [TensorProduct.smul_tmul']
  simp [smul_smul, mul_comm]

end QuaternionNorm

section ConcreteUnit

variable {k : Type u} [CommRing k] [StarRing k] [TrivialStar k]

/-- The concrete self-adjoint unit really has coefficient `j ⊗ j'`. -/
@[simp] theorem jTensorSelfAdjointUnit_val
    (p q : QuaternionParameters k) (hp : JUnitData p) (hq : JUnitData q) :
    (jTensorSelfAdjointUnit p q hp hq).val =
      PresentedQuaternion.j p ⊗ₜ[k] PresentedQuaternion.j q := rfl

/-- Consequently the concrete self-adjoint coefficient has square
`c₃c₃'` inside the biquaternion algebra. -/
@[simp] theorem jTensorSelfAdjointUnit_val_mul_self
    (p q : QuaternionParameters k) (hp : JUnitData p) (hq : JUnitData q) :
    (jTensorSelfAdjointUnit p q hp hq).val *
        (jTensorSelfAdjointUnit p q hp hq).val =
      algebraMap k (Biquaternion p q) (p.c₃ * q.c₃) := by
  exact jTensor_mul_self p q

end ConcreteUnit

end RiemannResearch.E7.QuaternionHermitian
