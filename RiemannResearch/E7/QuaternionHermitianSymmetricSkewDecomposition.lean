/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianQuadraticPair
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
# Symmetric-skew decomposition of the E7 quadratic pair

Away from characteristic two, every element of an algebra with involution
decomposes uniquely as the sum of its self-adjoint and skew-adjoint halves:

`x = (x + x⋆)/2 + (x - x⋆)/2`.

This file formalizes that decomposition as a linear equivalence. Applied to
the explicit degree-eight quadratic pair, it gives the complementary
dimension calculation

`64 = 36 + 28`.

Thus the concrete object now has the expected `36`-dimensional symmetric
space and `28`-dimensional skew space. No discriminant or generalized
Clifford-component calculation is asserted here.
-/

open scoped TensorProduct

namespace RiemannResearch.E7.QuaternionHermitian

universe u v

section Half

variable {k : Type u} [Field k]
variable {A : Type v} [AddCommGroup A] [Module k A]

/-- Multiplication by one half inverts doubling when `2` is nonzero. -/
lemma invTwo_smul_add_self [NeZero (2 : k)] (x : A) :
    (2 : k)⁻¹ • (x + x) = x := by
  rw [← two_smul k x, smul_smul,
    inv_mul_cancel₀ (NeZero.ne (2 : k)), one_smul]

end Half

section Projections

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]
variable {A : Type v} [Ring A] [Algebra k A] [StarRing A] [StarModule k A]

/-- Projection to the self-adjoint subspace by `x ↦ (x + x⋆)/2`. -/
noncomputable def halfSymmetricProjection [NeZero (2 : k)] :
    A →ₗ[k] symmetricSubmodule (k := k) (A := A) where
  toFun x := ⟨(2 : k)⁻¹ • (x + star x), by
    change star ((2 : k)⁻¹ • (x + star x)) =
      (2 : k)⁻¹ • (x + star x)
    rw [StarModule.star_smul, TrivialStar.star_trivial, star_add, star_star]
    exact congrArg ((2 : k)⁻¹ • ·) (add_comm _ _)⟩
  map_add' x y := by
    apply Subtype.ext
    change (2 : k)⁻¹ • ((x + y) + star (x + y)) =
      (2 : k)⁻¹ • (x + star x) + (2 : k)⁻¹ • (y + star y)
    simp only [star_add, smul_add]
    abel
  map_smul' r x := by
    apply Subtype.ext
    change (2 : k)⁻¹ • (r • x + star (r • x)) =
      r • ((2 : k)⁻¹ • (x + star x))
    rw [StarModule.star_smul, TrivialStar.star_trivial]
    simp only [smul_add, smul_smul]
    rw [mul_comm (2 : k)⁻¹ r]

/-- Projection to the skew-adjoint subspace by `x ↦ (x - x⋆)/2`. -/
noncomputable def halfSkewProjection [NeZero (2 : k)] :
    A →ₗ[k] skewSubmodule (k := k) (A := A) where
  toFun x := ⟨(2 : k)⁻¹ • (x - star x), by
    change star ((2 : k)⁻¹ • (x - star x)) =
      -((2 : k)⁻¹ • (x - star x))
    rw [StarModule.star_smul, TrivialStar.star_trivial, star_sub, star_star]
    simp only [smul_sub]
    abel⟩
  map_add' x y := by
    apply Subtype.ext
    change (2 : k)⁻¹ • ((x + y) - star (x + y)) =
      (2 : k)⁻¹ • (x - star x) + (2 : k)⁻¹ • (y - star y)
    simp only [star_add, smul_sub, smul_add]
    abel
  map_smul' r x := by
    apply Subtype.ext
    change (2 : k)⁻¹ • (r • x - star (r • x)) =
      r • ((2 : k)⁻¹ • (x - star x))
    rw [StarModule.star_smul, TrivialStar.star_trivial]
    simp only [smul_sub, smul_smul]
    rw [mul_comm (2 : k)⁻¹ r]

@[simp] theorem halfSymmetricProjection_val [NeZero (2 : k)] (x : A) :
    ((halfSymmetricProjection x :
      symmetricSubmodule (k := k) (A := A)) : A) =
      (2 : k)⁻¹ • (x + star x) :=
  rfl

@[simp] theorem halfSkewProjection_val [NeZero (2 : k)] (x : A) :
    ((halfSkewProjection x :
      skewSubmodule (k := k) (A := A)) : A) =
      (2 : k)⁻¹ • (x - star x) :=
  rfl

/-- The direct-sum decomposition into self-adjoint and skew-adjoint parts. -/
noncomputable def symmetricSkewLinearEquiv [NeZero (2 : k)] :
    A ≃ₗ[k]
      symmetricSubmodule (k := k) (A := A) ×
        skewSubmodule (k := k) (A := A) where
  toFun x := (halfSymmetricProjection x, halfSkewProjection x)
  invFun p := p.1.1 + p.2.1
  left_inv x := by
    change (2 : k)⁻¹ • (x + star x) +
      (2 : k)⁻¹ • (x - star x) = x
    rw [← smul_add]
    have h : (x + star x) + (x - star x) = x + x := by abel
    rw [h, invTwo_smul_add_self]
  right_inv p := by
    rcases p with ⟨s, a⟩
    apply Prod.ext
    · apply Subtype.ext
      change (2 : k)⁻¹ • ((s.1 + a.1) + star (s.1 + a.1)) = s.1
      rw [star_add, s.property, a.property]
      have h : (s.1 + a.1) + (s.1 + -a.1) = s.1 + s.1 := by abel
      rw [h, invTwo_smul_add_self]
    · apply Subtype.ext
      change (2 : k)⁻¹ • ((s.1 + a.1) - star (s.1 + a.1)) = a.1
      rw [star_add, s.property, a.property]
      have h : (s.1 + a.1) - (s.1 + -a.1) = a.1 + a.1 := by abel
      rw [h, invTwo_smul_add_self]
  map_add' x y := by
    exact Prod.ext
      ((halfSymmetricProjection :
        A →ₗ[k] symmetricSubmodule (k := k) (A := A)).map_add x y)
      ((halfSkewProjection :
        A →ₗ[k] skewSubmodule (k := k) (A := A)).map_add x y)
  map_smul' r x := by
    exact Prod.ext
      ((halfSymmetricProjection :
        A →ₗ[k] symmetricSubmodule (k := k) (A := A)).map_smul r x)
      ((halfSkewProjection :
        A →ₗ[k] skewSubmodule (k := k) (A := A)).map_smul r x)

/-- Every element is the sum of its two canonical halves. -/
theorem halfSymmetric_add_halfSkew [NeZero (2 : k)] (x : A) :
    (halfSymmetricProjection x :
        symmetricSubmodule (k := k) (A := A)).1 +
      (halfSkewProjection x :
        skewSubmodule (k := k) (A := A)).1 = x :=
  (symmetricSkewLinearEquiv (k := k) (A := A)).left_inv x

end Projections

namespace DegreeEightQuadraticPair

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]
variable {A : Type v} [Ring A] [Algebra k A] [StarRing A] [StarModule k A]

/-- The skew-adjoint subspace of a degree-eight quadratic pair has dimension
`28`, complementary to the verified symmetric dimension `36`. -/
theorem skew_finrank [NeZero (2 : k)]
    (P : DegreeEightQuadraticPair k A) :
    Module.finrank k (skewSubmodule (k := k) (A := A)) = 28 := by
  let : FiniteDimensional k A := P.finiteDimensional
  have h := LinearEquiv.finrank_eq
    (symmetricSkewLinearEquiv (k := k) (A := A))
  rw [Module.finrank_prod, P.algebra_finrank, P.symmetric_finrank] at h
  omega

end DegreeEightQuadraticPair

end RiemannResearch.E7.QuaternionHermitian
