/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianSemiTrace
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.FinCases

/-!
# Symmetric subspaces of the degree-eight hermitian adjoint algebra

This file isolates the linear-algebra part of the orthogonal-type calculation
for the degree-eight E7 hermitian construction.

Left multiplication by the Gram matrix identifies the self-adjoint subspace
of the hermitian adjoint algebra with the self-adjoint subspace of the
ordinary matrix algebra. For two-by-two matrices, the latter splits into two
copies of the self-adjoint subspace of the coefficient algebra and one
unrestricted off-diagonal coefficient.

Consequently the remaining orthogonal-type dimension calculation is reduced
to the canonical involution on the biquaternion coefficient algebra. No
Clifford-component statement is asserted here.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u v w

section GramTransport

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {A : Type w} [Ring A] [Algebra k A] [StarRing A] [StarModule k A]

namespace HermitianGram

/-- Left multiplication by the Gram matrix is a linear equivalence from the
packaged adjoint algebra to its underlying matrix algebra. -/
noncomputable def leftMulEquiv
    (G : HermitianGram (ι := ι) (A := A)) :
    AdjointAlgebra G ≃ₗ[k] Matrix ι ι A where
  toFun x := G.matrix * x.val
  invFun X := ⟨G.inverse * X⟩
  map_add' x y := by
    simp [mul_add]
  map_smul' r x := by
    simp [Algebra.mul_smul_comm]
  left_inv x := by
    apply AdjointAlgebra.ext
    change G.inverse * (G.matrix * x.val) = x.val
    rw [← mul_assoc, G.inverse_mul_matrix, one_mul]
  right_inv X := by
    change G.matrix * (G.inverse * X) = X
    rw [← mul_assoc, G.matrix_mul_inverse, one_mul]

/-- Left multiplication by the Gram matrix restricts to an equivalence of
self-adjoint subspaces. Thus the dimension of the symmetric subspace is
independent of the chosen invertible hermitian Gram matrix. -/
noncomputable def symmetricEquiv
    (G : HermitianGram (ι := ι) (A := A)) :
    symmetricSubmodule (k := k) (A := AdjointAlgebra G) ≃ₗ[k]
      symmetricSubmodule (k := k) (A := Matrix ι ι A) where
  toFun x := ⟨G.matrix * x.1.val, by
    change star (G.matrix * x.1.val) = G.matrix * x.1.val
    have hx := congrArg AdjointAlgebra.val x.2
    change G.inverse * star x.1.val * G.matrix = x.1.val at hx
    have hmul := congrArg (fun Y : Matrix ι ι A => G.matrix * Y) hx
    simp only [← mul_assoc, G.matrix_mul_inverse, one_mul] at hmul
    rw [StarMul.star_mul, G.star_matrix]
    exact hmul⟩
  invFun y := ⟨⟨G.inverse * y.1⟩, by
    apply AdjointAlgebra.ext
    change G.inverse * star (G.inverse * y.1) * G.matrix = G.inverse * y.1
    rw [StarMul.star_mul, G.star_inverse, y.2]
    simp only [mul_assoc]
    rw [G.inverse_mul_matrix, mul_one]⟩
  map_add' x y := by
    apply Subtype.ext
    simp [mul_add]
  map_smul' r x := by
    apply Subtype.ext
    simp [Algebra.mul_smul_comm]
  left_inv x := by
    apply Subtype.ext
    apply AdjointAlgebra.ext
    change G.inverse * (G.matrix * x.1.val) = x.1.val
    rw [← mul_assoc, G.inverse_mul_matrix, one_mul]
  right_inv y := by
    apply Subtype.ext
    change G.matrix * (G.inverse * y.1) = y.1
    rw [← mul_assoc, G.matrix_mul_inverse, one_mul]

theorem symmetricSubmodule_finrank_eq_matrix
    (G : HermitianGram (ι := ι) (A := A)) :
    Module.finrank k
        (symmetricSubmodule (k := k) (A := AdjointAlgebra G)) =
      Module.finrank k
        (symmetricSubmodule (k := k) (A := Matrix ι ι A)) :=
  (symmetricEquiv G).finrank_eq

end HermitianGram

end GramTransport

section TwoByTwo

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]
variable {A : Type v} [Ring A] [Algebra k A] [StarRing A] [StarModule k A]

/-- A self-adjoint two-by-two matrix consists of two self-adjoint diagonal
entries and one arbitrary upper-right entry; the lower-left entry is forced
to be its adjoint. -/
noncomputable def finTwoMatrixSymmetricEquiv :
    symmetricSubmodule (k := k) (A := Matrix (Fin 2) (Fin 2) A) ≃ₗ[k]
      symmetricSubmodule (k := k) (A := A) ×
        (A × symmetricSubmodule (k := k) (A := A)) where
  toFun X :=
    (⟨X.1 0 0, by
      have h := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) A => M 0 0) X.2
      change star (X.1 0 0) = X.1 0 0 at h
      exact h⟩,
     (X.1 0 1,
      ⟨X.1 1 1, by
        have h := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) A => M 1 1) X.2
        change star (X.1 1 1) = X.1 1 1 at h
        exact h⟩))
  invFun Y :=
    ⟨![![Y.1.1, Y.2.1], ![star Y.2.1, Y.2.2.1]], by
      ext i j
      fin_cases i <;> fin_cases j
      · change star Y.1.1 = Y.1.1
        exact Y.1.2
      · change star (star Y.2.1) = Y.2.1
        simp
      · change star Y.2.1 = star Y.2.1
        rfl
      · change star Y.2.2.1 = Y.2.2.1
        exact Y.2.2.2⟩
  map_add' X Y := by
    ext <;> rfl
  map_smul' r X := by
    ext <;> simp
  left_inv X := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · have h := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) A => M 1 0) X.2
      change star (X.1 0 1) = X.1 1 0 at h
      exact h
    · rfl
  right_inv Y := by
    rfl

theorem finTwoMatrixSymmetric_finrank
    [Module.Finite k A] :
    Module.finrank k
        (symmetricSubmodule (k := k) (A := Matrix (Fin 2) (Fin 2) A)) =
      Module.finrank k (symmetricSubmodule (k := k) (A := A)) +
        (Module.finrank k A +
          Module.finrank k (symmetricSubmodule (k := k) (A := A))) := by
  calc
    _ = Module.finrank k
        (symmetricSubmodule (k := k) (A := A) ×
          (A × symmetricSubmodule (k := k) (A := A))) :=
      finTwoMatrixSymmetricEquiv.finrank_eq
    _ = _ := by rw [Module.finrank_prod, Module.finrank_prod]

/-- The symmetric dimension of a rank-two hermitian adjoint is twice the
symmetric dimension of the coefficient algebra plus its full dimension. -/
theorem degreeEightAdjointSymmetric_finrank_formula
    (p q : QuaternionParameters k)
    (G : DegreeEightHermitianGram p q) :
    Module.finrank k
        (symmetricSubmodule
          (k := k) (A := DegreeEightAdjointAlgebra p q G)) =
      Module.finrank k
          (symmetricSubmodule (k := k) (A := Biquaternion p q)) +
        (Module.finrank k (Biquaternion p q) +
          Module.finrank k
            (symmetricSubmodule (k := k) (A := Biquaternion p q))) := by
  rw [HermitianGram.symmetricSubmodule_finrank_eq_matrix G]
  exact finTwoMatrixSymmetric_finrank

end TwoByTwo

end RiemannResearch.E7.QuaternionHermitian
