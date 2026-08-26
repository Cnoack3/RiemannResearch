/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import RiemannResearch.AlgebraicGeometry.SpecialLinearTwoCoordinateRing

/-!
# Cogroup maps on the integral coordinate ring of split `SL₂`

The represented `SL₂` functor is group-valued.  This file constructs the
corresponding coordinate comultiplication, counit, and antipode from the
product, identity, and inverse of universal points.

The downstream Hopf module proves the coherence laws and installs Mathlib's
`Bialgebra` and `HopfAlgebra` instances.
-/

namespace RiemannResearch
namespace AlgebraicGeometry
namespace SpecialLinearTwo

noncomputable section

open scoped TensorProduct

private abbrev A := Coordinate
private abbrev T := A ⊗[ℤ] A

local instance coordinateAddCommMonoid : AddCommMonoid A :=
  (inferInstance : Semiring A).toAddCommMonoid

local instance coordinateIntModule : Module ℤ A :=
  @Algebra.toModule ℤ A _ _ (inferInstance : Algebra ℤ A)

/-- Ring structure on the tensor square of the coordinate ring. -/
@[instance_reducible]
noncomputable def tensorProductRing : Ring T := by
  let sr : Semiring T := inferInstance
  let ag : AddCommGroup T := inferInstance
  exact { sr, ag with
    intCast := Int.castDef
    intCast_ofNat := by intro n; rfl
    intCast_negSucc := by intro n; rfl }

noncomputable local instance : Ring T :=
  tensorProductRing

/-- Commutative-ring structure on the tensor square. -/
@[instance_reducible]
noncomputable def tensorProductCommRing : CommRing T := by
  let cr : CommSemiring T :=
    Algebra.TensorProduct.instCommSemiring
  exact { tensorProductRing, cr with }

noncomputable local instance : CommRing T :=
  tensorProductCommRing

local instance tensorCanonicalIntAlgebra : Algebra ℤ T :=
  @Algebra.TensorProduct.instAlgebra ℤ A A
    (inferInstance : CommSemiring ℤ)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)

/-- Package a coordinate-ring map as an integer-algebra map. -/
def coordinateAlgHomOfRingHom
    {R : Type} [CommRing R] [Algebra ℤ R]
    (f : A →+* R) : A →ₐ[ℤ] R where
  toRingHom := f
  commutes' z := by simp

/-- Two integer-algebra maps out of the coordinate ring are equal when they
send the universal `SL₂`-point to the same point. -/
theorem coordinateAlgHom_ext
    {R : Type} [CommRing R] [Algebra ℤ R]
    (f g : A →ₐ[ℤ] R)
    (h : Matrix.SpecialLinearGroup.map f.toRingHom universalPoint =
      Matrix.SpecialLinearGroup.map g.toRingHom universalPoint) :
    f = g := by
  apply AlgHom.ext
  intro x
  have he : f.toRingHom = g.toRingHom := by
    rw [← coordinateEvaluation_baseChange f.toRingHom,
      ← coordinateEvaluation_baseChange g.toRingHom, h]
  exact DFunLike.congr_fun he x

/-- Inclusion of the first tensor factor. -/
def tensorIncludeLeft : A →+* T :=
  Algebra.TensorProduct.includeLeftRingHom

/-- Inclusion of the second tensor factor. -/
def tensorIncludeRight : A →+* T where
  toFun x := (1 : A) ⊗ₜ[ℤ] x
  map_one' := by
    exact (Algebra.TensorProduct.one_def :
      (1 : T) = (1 : A) ⊗ₜ[ℤ] (1 : A)).symm
  map_mul' x y := by
    have h :
        ((1 : A) ⊗ₜ[ℤ] x) * ((1 : A) ⊗ₜ[ℤ] y) =
          ((1 : A) * 1) ⊗ₜ[ℤ] (x * y) :=
      Algebra.TensorProduct.tmul_mul_tmul _ _ _ _
    rw [show (1 : A) * 1 = 1 by exact mul_one (1 : A)] at h
    exact h.symm
  map_zero' := TensorProduct.tmul_zero A (1 : A)
  map_add' x y := TensorProduct.tmul_add (1 : A) x y

/-- Universal point in the first tensor factor. -/
def universalPointLeft : Matrix.SpecialLinearGroup (Fin 2) T :=
  Matrix.SpecialLinearGroup.map tensorIncludeLeft universalPoint

/-- Universal point in the second tensor factor. -/
def universalPointRight : Matrix.SpecialLinearGroup (Fin 2) T :=
  Matrix.SpecialLinearGroup.map tensorIncludeRight universalPoint

/-- Product of the two universal tensor-factor points. -/
def universalPointProduct : Matrix.SpecialLinearGroup (Fin 2) T :=
  universalPointLeft * universalPointRight

/-- Coordinate comultiplication induced by multiplication in `SL₂`. -/
def coordinateComul : A →ₐ[ℤ] T :=
  coordinateAlgHomOfRingHom
    (coordinateEvaluation universalPointProduct)

/-- Coordinate counit induced by the identity point. -/
def coordinateCounit : A →ₐ[ℤ] ℤ :=
  coordinateAlgHomOfRingHom
    (coordinateEvaluation
      (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))

/-- Coordinate antipode induced by inversion of the universal point. -/
def coordinateAntipode : A →ₐ[ℤ] A :=
  coordinateAlgHomOfRingHom
    (coordinateEvaluation universalPoint⁻¹)

/-- Comultiplication sends the universal point to the universal product. -/
theorem coordinateComul_universal :
    Matrix.SpecialLinearGroup.map coordinateComul.toRingHom universalPoint =
      universalPointProduct := by
  change Matrix.SpecialLinearGroup.map
    (coordinateEvaluation universalPointProduct) universalPoint =
      universalPointProduct
  exact coordinateEvaluation_universal universalPointProduct

/-- Counit sends the universal point to the identity. -/
theorem coordinateCounit_universal :
    Matrix.SpecialLinearGroup.map coordinateCounit.toRingHom universalPoint =
      (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
  change Matrix.SpecialLinearGroup.map
    (coordinateEvaluation
      (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) universalPoint = 1
  exact coordinateEvaluation_universal _

/-- Antipode sends the universal point to its inverse. -/
theorem coordinateAntipode_universal :
    Matrix.SpecialLinearGroup.map coordinateAntipode.toRingHom universalPoint =
      universalPoint⁻¹ := by
  exact coordinateEvaluation_universal _

end

end SpecialLinearTwo
end AlgebraicGeometry
end RiemannResearch
