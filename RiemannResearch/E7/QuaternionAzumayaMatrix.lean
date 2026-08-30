/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianDegreeEight
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Canonical left-right matrix for a uniform quaternion algebra

For Mathlib's uniform quaternion presentation

`QuaternionAlgebra k c₁ c₂ c₃`,

this file computes the matrix of the canonical left-right action

`A ⊗[k] Aᵐᵒᵖ →ₐ[k] Module.End k A`

in the ordered basis `(1, i, j, k)`. It also gives a polynomial
scaled inverse `S` and verifies both identities

`M S = S M = c₃ (4 c₁ + c₂²) I₁₆`.

The calculation is valid in every characteristic. Consequently the
coordinate matrix is invertible whenever `c₃ ≠ 0` and
`4 c₁ + c₂² ≠ 0`.

This file links the displayed matrix to the actual Mathlib algebra map.
The subsequent Azumaya layer transports this coordinate certificate back
to `AlgHom.mulLeftRight`.
-/

open TensorProduct MulOpposite

namespace RiemannResearch.E7.QuaternionHermitian
namespace QuaternionAzumayaMatrix

universe u

variable {k : Type u} [Field k]

abbrev Pair4 := Fin 4 × Fin 4

/-- Explicit row-major identification `(Fin 4 × Fin 4) ≃ Fin 16`. -/
def pair4EquivFin16 : Pair4 ≃ Fin 16 where
  toFun p := ![
    ![(0 : Fin 16), 1, 2, 3],
    ![(4 : Fin 16), 5, 6, 7],
    ![(8 : Fin 16), 9, 10, 11],
    ![(12 : Fin 16), 13, 14, 15]
  ] p.1 p.2
  invFun i := ![
    ((0 : Fin 4), (0 : Fin 4)), (0, 1), (0, 2), (0, 3),
    (1, 0), (1, 1), (1, 2), (1, 3),
    (2, 0), (2, 1), (2, 2), (2, 3),
    (3, 0), (3, 1), (3, 2), (3, 3)
  ] i
  left_inv := by
    rintro ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- The ordered quaternion basis `(1, i, j, k)`. -/
noncomputable def quaternionBasis (p : QuaternionParameters k) :
    Module.Basis (Fin 4) k (PresentedQuaternion p) :=
  QuaternionAlgebra.basisOneIJK p.c₁ p.c₂ p.c₃

@[simp] theorem quaternionBasis_re (p : QuaternionParameters k) (i : Fin 4) :
    (quaternionBasis p i).re = if i = 0 then 1 else 0 := by
  have h := congrFun
    (QuaternionAlgebra.coe_basisOneIJK_repr p.c₁ p.c₂ p.c₃
      (quaternionBasis p i)) 0
  simpa [quaternionBasis, Finsupp.single_apply, eq_comm] using h.symm

@[simp] theorem quaternionBasis_imI (p : QuaternionParameters k) (i : Fin 4) :
    (quaternionBasis p i).imI = if i = 1 then 1 else 0 := by
  have h := congrFun
    (QuaternionAlgebra.coe_basisOneIJK_repr p.c₁ p.c₂ p.c₃
      (quaternionBasis p i)) 1
  simpa [quaternionBasis, Finsupp.single_apply, eq_comm] using h.symm

@[simp] theorem quaternionBasis_imJ (p : QuaternionParameters k) (i : Fin 4) :
    (quaternionBasis p i).imJ = if i = 2 then 1 else 0 := by
  have h := congrFun
    (QuaternionAlgebra.coe_basisOneIJK_repr p.c₁ p.c₂ p.c₃
      (quaternionBasis p i)) 2
  simpa [quaternionBasis, Finsupp.single_apply, eq_comm] using h.symm

@[simp] theorem quaternionBasis_imK (p : QuaternionParameters k) (i : Fin 4) :
    (quaternionBasis p i).imK = if i = 3 then 1 else 0 := by
  have h := congrFun
    (QuaternionAlgebra.coe_basisOneIJK_repr p.c₁ p.c₂ p.c₃
      (quaternionBasis p i)) 3
  simpa [quaternionBasis, Finsupp.single_apply, eq_comm] using h.symm

@[simp] theorem quaternionBasis_repr_apply (p : QuaternionParameters k)
    (x : PresentedQuaternion p) (i : Fin 4) :
    (quaternionBasis p).repr x i = ![x.re, x.imI, x.imJ, x.imK] i := by
  have h := congrFun
    (QuaternionAlgebra.coe_basisOneIJK_repr p.c₁ p.c₂ p.c₃ x) i
  simpa [quaternionBasis] using h

/-- The corresponding basis on the opposite algebra. -/
noncomputable def quaternionOppositeBasis (p : QuaternionParameters k) :
    Module.Basis (Fin 4) k (PresentedQuaternion p)ᵐᵒᵖ :=
  (quaternionBasis p).map (MulOpposite.opLinearEquiv k)

/-- The row-major tensor basis of `A ⊗ Aᵐᵒᵖ`. -/
noncomputable def quaternionTensorBasis (p : QuaternionParameters k) :
    Module.Basis Pair4 k
      ((PresentedQuaternion p) ⊗[k] (PresentedQuaternion p)ᵐᵒᵖ) :=
  (quaternionBasis p).tensorProduct (quaternionOppositeBasis p)

/-- Flatten a `4 × 4` matrix using output coordinate first. -/
noncomputable def matrixUncurry :
    Matrix (Fin 4) (Fin 4) k ≃ₗ[k] (Pair4 → k) :=
  (LinearEquiv.curry k k (Fin 4) (Fin 4)).symm

@[simp] theorem matrixUncurry_apply
    (M : Matrix (Fin 4) (Fin 4) k) (i j : Fin 4) :
    matrixUncurry M (i, j) = M i j := rfl

/-- Coordinate form of the canonical left-right action. -/
noncomputable def canonicalVectorMap (p : QuaternionParameters k) :
    (Pair4 → k) →ₗ[k] (Pair4 → k) :=
  (matrixUncurry (k := k)).toLinearMap.comp <|
    (LinearMap.toMatrix (quaternionBasis p)
      (quaternionBasis p)).toLinearMap.comp <|
      (AlgHom.mulLeftRight k (PresentedQuaternion p)).toLinearMap.comp <|
        (quaternionTensorBasis p).equivFun.symm.toLinearMap

/-- A column of the canonical matrix is obtained by multiplying a basis
element on the left and on the right. -/
theorem canonicalVectorMap_single (p : QuaternionParameters k)
    (a b i j : Fin 4) :
    canonicalVectorMap p (Pi.single (a, b) 1) (i, j) =
      ((quaternionBasis p).repr
        ((quaternionBasis p a) * (quaternionBasis p j) *
          (quaternionBasis p b))) i := by
  change matrixUncurry
    ((LinearMap.toMatrix (quaternionBasis p) (quaternionBasis p))
      ((AlgHom.mulLeftRight k (PresentedQuaternion p))
        ((quaternionTensorBasis p).equivFun.symm
          (Pi.single (a, b) 1)))) (i, j) = _
  rw [matrixUncurry_apply, LinearMap.toMatrix_apply]
  simp [quaternionTensorBasis, quaternionOppositeBasis,
    AlgHom.mulLeftRight_apply]

/-- Matrix of `canonicalVectorMap` in the standard basis on pair-indexed
coordinate vectors. -/
noncomputable def canonicalPairMatrix (p : QuaternionParameters k) :
    Matrix Pair4 Pair4 k :=
  (LinearMap.toMatrix (Pi.basisFun k Pair4) (Pi.basisFun k Pair4))
    (canonicalVectorMap p)

theorem canonicalPairMatrix_apply (p : QuaternionParameters k)
    (r c : Pair4) :
    canonicalPairMatrix p r c =
      canonicalVectorMap p (Pi.single c 1) r := by
  rw [canonicalPairMatrix, LinearMap.toMatrix_apply]
  simp

/-- Row-major reindexing of the actual canonical matrix. -/
noncomputable def canonicalFlatMatrix (p : QuaternionParameters k) :
    Matrix (Fin 16) (Fin 16) k :=
  (Matrix.reindex pair4EquivFin16 pair4EquivFin16)
    (canonicalPairMatrix p)

/-- The explicit canonical left-right matrix for parameters `(a,b,c)`. -/
def uniformQuaternionCanonicalMatrix (a b c : k) :
    Matrix (Fin 16) (Fin 16) k :=
  ![
    ![1, 0, 0, 0, 0, a, 0, 0, 0, 0, c, b*c, 0, 0, 0, -a*c],
    ![0, a, 0, 0, a, a*b, 0, 0, 0, 0, b*c, a*c + b ^ 2*c, 0, 0, -a*c, -a*b*c],
    ![0, 0, c, b*c, 0, 0, 0, -a*c, c, 0, 0, 0, 0, a*c, 0, 0],
    ![0, 0, 0, -a*c, 0, 0, a*c, 0, b*c, -a*c, 0, 0, -a*c, 0, 0, 0],
    ![0, 1, 0, 0, 1, b, 0, 0, 0, 0, 0, -c, 0, 0, c, 0],
    ![1, b, 0, 0, b, a + b ^ 2, 0, 0, 0, 0, -c, -b*c, 0, 0, 0, a*c],
    ![0, 0, 0, -c, 0, 0, c, 0, 0, c, 0, 0, c, b*c, 0, 0],
    ![0, 0, c, 0, 0, 0, b*c, -a*c, -c, 0, 0, 0, 0, -a*c, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, a, 1, b, 0, 0, 0, -a, 0, 0],
    ![0, 0, 0, a, 0, 0, a, a*b, b, a + b ^ 2, 0, 0, -a, -a*b, 0, 0],
    ![1, b, 0, 0, 0, -a, 0, 0, 0, 0, c, 0, 0, 0, 0, a*c],
    ![0, -a, 0, 0, a, 0, 0, 0, 0, 0, b*c, -a*c, 0, 0, -a*c, 0],
    ![0, 0, 0, 1, 0, 0, 1, b, 0, -1, 0, 0, 1, 0, 0, 0],
    ![0, 0, 1, b, 0, 0, b, a + b ^ 2, -1, -b, 0, 0, 0, a, 0, 0],
    ![0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, c, 0, 0, c, b*c],
    ![1, 0, 0, 0, b, -a, 0, 0, 0, 0, -c, 0, 0, 0, 0, -a*c]
  ]

/-- Polynomial scaled inverse of `uniformQuaternionCanonicalMatrix`. -/
def uniformQuaternionScaledInverseMatrix (a b c : k) :
    Matrix (Fin 16) (Fin 16) k :=
  ![
    ![c*(a + b ^ 2), -b*c, 0, 0, -a*b*c, a*c, 0, 0, 0, 0, a*c, 0, 0, 0, 0, a*c],
    ![-b*c, c, 0, 0, a*c, 0, 0, 0, 0, 0, b*c, -c, 0, 0, -a*c, 0],
    ![0, 0, a, 0, 0, 0, 0, a, c*(a + b ^ 2), -b*c, 0, 0, -a*b*c, a*c, 0, 0],
    ![0, 0, b, -1, 0, 0, -a, 0, -b*c, c, 0, 0, a*c, 0, 0, 0],
    ![-b*c, c, 0, 0, a*c, 0, 0, 0, 0, 0, 0, c, 0, 0, a*c, b*c],
    ![c, 0, 0, 0, 0, c, 0, 0, 0, 0, -c, 0, 0, 0, 0, -c],
    ![0, 0, 0, 1, 0, 0, a, b, -b*c, c, 0, 0, a*c, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0, 0, -1, c, 0, 0, 0, 0, c, 0, 0],
    ![0, 0, a, b, 0, 0, 0, -a, a*c, 0, 0, 0, a*b*c, -a*c, 0, 0],
    ![0, 0, 0, -1, 0, 0, a, 0, 0, c, 0, 0, -a*c, 0, 0, 0],
    ![a, 0, 0, 0, a*b, -a, 0, 0, 0, 0, a, b, 0, 0, 0, -a],
    ![0, 1, 0, 0, -a, 0, 0, 0, 0, 0, 0, -1, 0, 0, a, 0],
    ![0, 0, 0, -1, 0, 0, a, 0, b*c, -c, 0, 0, c*(a + b ^ 2), -b*c, 0, 0],
    ![0, 0, 1, 0, 0, 0, b, -1, -c, 0, 0, 0, -b*c, c, 0, 0],
    ![b, -1, 0, 0, a + b ^ 2, -b, 0, 0, 0, 0, 0, -1, 0, 0, a, 0],
    ![-1, 0, 0, 0, -b, 1, 0, 0, 0, 0, 1, 0, 0, 0, b, -1]
  ]

set_option maxHeartbeats 3000000 in
/-- The displayed matrix is the actual canonical left-right matrix. -/
theorem canonicalFlatMatrix_eq_uniform
    (p : QuaternionParameters k) :
    canonicalFlatMatrix p =
      uniformQuaternionCanonicalMatrix p.c₁ p.c₂ p.c₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalFlatMatrix, pair4EquivFin16, Matrix.reindex_apply,
      canonicalPairMatrix_apply, canonicalVectorMap_single,
      uniformQuaternionCanonicalMatrix] <;> ring

set_option maxHeartbeats 3000000 in
/-- Right scaled-inverse identity. -/
theorem canonical_mul_scaledInverse (a b c : k) :
    uniformQuaternionCanonicalMatrix a b c *
        uniformQuaternionScaledInverseMatrix a b c =
      (c * (4 * a + b ^ 2)) •
        (1 : Matrix (Fin 16) (Fin 16) k) := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [uniformQuaternionCanonicalMatrix,
      uniformQuaternionScaledInverseMatrix, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 3000000 in
/-- Left scaled-inverse identity. -/
theorem scaledInverse_mul_canonical (a b c : k) :
    uniformQuaternionScaledInverseMatrix a b c *
        uniformQuaternionCanonicalMatrix a b c =
      (c * (4 * a + b ^ 2)) •
        (1 : Matrix (Fin 16) (Fin 16) k) := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [uniformQuaternionCanonicalMatrix,
      uniformQuaternionScaledInverseMatrix, Fin.sum_univ_succ] <;> ring

/-- The genuine inverse matrix under the nondegeneracy scalar. -/
noncomputable def uniformQuaternionInverseMatrix (a b c : k) :
    Matrix (Fin 16) (Fin 16) k :=
  (c * (4 * a + b ^ 2))⁻¹ •
    uniformQuaternionScaledInverseMatrix a b c

theorem canonical_mul_inverse (a b c : k)
    (h : c * (4 * a + b ^ 2) ≠ 0) :
    uniformQuaternionCanonicalMatrix a b c *
        uniformQuaternionInverseMatrix a b c = 1 := by
  rw [uniformQuaternionInverseMatrix, Matrix.mul_smul,
    canonical_mul_scaledInverse, smul_smul, inv_mul_cancel₀ h, one_smul]

theorem inverse_mul_canonical (a b c : k)
    (h : c * (4 * a + b ^ 2) ≠ 0) :
    uniformQuaternionInverseMatrix a b c *
        uniformQuaternionCanonicalMatrix a b c = 1 := by
  rw [uniformQuaternionInverseMatrix, Matrix.smul_mul,
    scaledInverse_mul_canonical, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- The explicit canonical matrix acts bijectively on coordinate vectors
under the two nondegeneracy conditions. -/
theorem canonical_mulVec_bijective (a b c : k)
    (h : c * (4 * a + b ^ 2) ≠ 0) :
    Function.Bijective
      (Matrix.mulVec (uniformQuaternionCanonicalMatrix a b c)) := by
  let N := uniformQuaternionInverseMatrix a b c
  have hMN :
      uniformQuaternionCanonicalMatrix a b c * N = 1 :=
    canonical_mul_inverse a b c h
  have hNM :
      N * uniformQuaternionCanonicalMatrix a b c = 1 :=
    inverse_mul_canonical a b c h
  constructor
  · intro x y hxy
    have hxy' := congrArg (Matrix.mulVec N) hxy
    simpa [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec] using hxy'
  · intro y
    refine ⟨Matrix.mulVec N y, ?_⟩
    simp [Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]

/-- The actual row-major canonical matrix is bijective under the expected
uniform-quaternion nondegeneracy hypotheses. -/
theorem canonicalFlatMatrix_mulVec_bijective
    (p : QuaternionParameters k)
    (hc : p.c₃ ≠ 0) (hdisc : 4 * p.c₁ + p.c₂ ^ 2 ≠ 0) :
    Function.Bijective (Matrix.mulVec (canonicalFlatMatrix p)) := by
  rw [canonicalFlatMatrix_eq_uniform]
  exact canonical_mulVec_bijective p.c₁ p.c₂ p.c₃
    (mul_ne_zero hc hdisc)

end QuaternionAzumayaMatrix
end RiemannResearch.E7.QuaternionHermitian
