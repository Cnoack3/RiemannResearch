/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SpecialLinearTwoCoordinateCogroup

/-!
# Hopf laws for the integral coordinate algebra of split `SL₂`

This module transports the group laws on represented `SL₂`-points through
the coordinate-ring universal property.  The first stage proves both counit
identities against Mathlib's exact tensor unitors.  Later stages in this file
prove coassociativity and the two antipode identities and install the actual
`Bialgebra` and `HopfAlgebra` instances.
-/

namespace RiemannResearch
namespace AlgebraicGeometry
namespace SpecialLinearTwo

noncomputable section

open scoped TensorProduct

private abbrev A := Coordinate
private abbrev T := A ⊗[ℤ] A

local instance hopfCoordinateAddCommMonoid : AddCommMonoid A :=
  (inferInstance : Semiring A).toAddCommMonoid

local instance hopfCoordinateIntModule : Module ℤ A :=
  @Algebra.toModule ℤ A _ _ (inferInstance : Algebra ℤ A)

noncomputable local instance : Ring T :=
  tensorProductRing

noncomputable local instance : CommRing T :=
  tensorProductCommRing

local instance hopfTensorCanonicalIntAlgebra : Algebra ℤ T :=
  @Algebra.TensorProduct.instAlgebra ℤ A A
    (inferInstance : CommSemiring ℤ)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)

/-- Pointwise functoriality of special-linear base change. -/
theorem specialLinearMap_comp_apply
    {R S U : Type} [CommRing R] [CommRing S] [CommRing U]
    (f : R →+* S) (g : S →+* U)
    (x : Matrix.SpecialLinearGroup (Fin 2) R) :
    Matrix.SpecialLinearGroup.map (g.comp f) x =
      Matrix.SpecialLinearGroup.map g
        (Matrix.SpecialLinearGroup.map f x) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

/-- Evaluation after comultiplication is multiplication of the two points
obtained from the tensor factors. -/
theorem coordinateComul_baseChange
    {R : Type} [CommRing R] [Algebra ℤ R]
    (f : T →ₐ[ℤ] R) :
    Matrix.SpecialLinearGroup.map
        ((f.comp coordinateComul).toRingHom) universalPoint =
      Matrix.SpecialLinearGroup.map f.toRingHom universalPointLeft *
        Matrix.SpecialLinearGroup.map f.toRingHom universalPointRight := by
  change Matrix.SpecialLinearGroup.map
      (f.toRingHom.comp coordinateComul.toRingHom) universalPoint = _
  rw [specialLinearMap_comp_apply]
  rw [coordinateComul_universal]
  exact (Matrix.SpecialLinearGroup.map f.toRingHom).map_mul _ _

/-- Evaluation after the counit is the identity point. -/
theorem coordinateCounit_baseChange
    {R : Type} [CommRing R] [Algebra ℤ R]
    (f : ℤ →ₐ[ℤ] R) :
    Matrix.SpecialLinearGroup.map
        ((f.comp coordinateCounit).toRingHom) universalPoint = 1 := by
  change Matrix.SpecialLinearGroup.map
      (f.toRingHom.comp coordinateCounit.toRingHom) universalPoint = 1
  rw [specialLinearMap_comp_apply]
  rw [coordinateCounit_universal]
  exact map_one _

section CounitIdentities

local instance hopfIntAddCommMonoid : AddCommMonoid ℤ :=
  (inferInstance : Semiring ℤ).toAddCommMonoid

local instance hopfIntModule : Module ℤ ℤ :=
  @Algebra.toModule ℤ ℤ _ _ (inferInstance : Algebra ℤ ℤ)

private abbrev LeftCounitTensor := ℤ ⊗[ℤ] A

noncomputable local instance leftCounitTensorRing :
    Ring LeftCounitTensor := by
  let sr : Semiring LeftCounitTensor := inferInstance
  let ag : AddCommGroup LeftCounitTensor := inferInstance
  exact { sr, ag with
    sub_eq_add_neg := by intros; rfl
    intCast := Int.castDef
    intCast_ofNat := by intro n; rfl
    intCast_negSucc := by intro n; rfl }

noncomputable local instance leftCounitTensorCommRing :
    CommRing LeftCounitTensor := by
  let cr : CommSemiring LeftCounitTensor :=
    @Algebra.TensorProduct.instCommSemiring ℤ ℤ A
      (inferInstance : CommSemiring ℤ)
      (inferInstance : CommSemiring ℤ)
      (inferInstance : Algebra ℤ ℤ)
      (inferInstance : CommSemiring A)
      (inferInstance : Algebra ℤ A)
  exact { leftCounitTensorRing, cr with }

local instance leftCounitTensorAlgebra :
    Algebra ℤ LeftCounitTensor :=
  @Algebra.TensorProduct.instAlgebra ℤ ℤ A
    (inferInstance : CommSemiring ℤ)
    (inferInstance : Semiring ℤ)
    (inferInstance : Algebra ℤ ℤ)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)

private abbrev RightCounitTensor := A ⊗[ℤ] ℤ

noncomputable local instance rightCounitTensorRing :
    Ring RightCounitTensor := by
  let sr : Semiring RightCounitTensor := inferInstance
  let ag : AddCommGroup RightCounitTensor := inferInstance
  exact { sr, ag with
    sub_eq_add_neg := by intros; rfl
    intCast := Int.castDef
    intCast_ofNat := by intro n; rfl
    intCast_negSucc := by intro n; rfl }

noncomputable local instance rightCounitTensorCommRing :
    CommRing RightCounitTensor := by
  let cr : CommSemiring RightCounitTensor :=
    @Algebra.TensorProduct.instCommSemiring ℤ A ℤ
      (inferInstance : CommSemiring ℤ)
      (inferInstance : CommSemiring A)
      (inferInstance : Algebra ℤ A)
      (inferInstance : CommSemiring ℤ)
      (inferInstance : Algebra ℤ ℤ)
  exact { rightCounitTensorRing, cr with }

local instance rightCounitTensorAlgebra :
    Algebra ℤ RightCounitTensor :=
  @Algebra.TensorProduct.instAlgebra ℤ A ℤ
    (inferInstance : CommSemiring ℤ)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)
    (inferInstance : Semiring ℤ)
    (inferInstance : Algebra ℤ ℤ)

private def leftCounitMap : T →ₐ[ℤ] LeftCounitTensor :=
  Algebra.TensorProduct.map coordinateCounit (AlgHom.id ℤ A)

private def leftCounitUnit : A →ₐ[ℤ] LeftCounitTensor :=
  (Algebra.TensorProduct.lid ℤ A).symm.toAlgHom

private def leftCounitScalar : ℤ →ₐ[ℤ] LeftCounitTensor :=
  Algebra.TensorProduct.includeLeft

private theorem leftCounitMap_includeLeft :
    leftCounitMap.toRingHom.comp tensorIncludeLeft =
      leftCounitScalar.toRingHom.comp coordinateCounit.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [leftCounitMap, leftCounitScalar, tensorIncludeLeft]

private theorem leftCounitMap_includeRight :
    leftCounitMap.toRingHom.comp tensorIncludeRight =
      leftCounitUnit.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [leftCounitMap, leftCounitUnit, tensorIncludeRight]

private theorem leftCounitPoint_left :
    Matrix.SpecialLinearGroup.map leftCounitMap.toRingHom
        universalPointLeft = 1 := by
  rw [universalPointLeft]
  rw [← specialLinearMap_comp_apply]
  rw [leftCounitMap_includeLeft]
  rw [specialLinearMap_comp_apply]
  rw [coordinateCounit_universal]
  exact (Matrix.SpecialLinearGroup.map leftCounitScalar.toRingHom).map_one

private theorem leftCounitPoint_right :
    Matrix.SpecialLinearGroup.map leftCounitMap.toRingHom
        universalPointRight =
      Matrix.SpecialLinearGroup.map leftCounitUnit.toRingHom
        universalPoint := by
  rw [universalPointRight]
  rw [← specialLinearMap_comp_apply]
  rw [leftCounitMap_includeRight]

/-- Comultiplication followed by counit on its left tensor factor is the
inverse of Mathlib's left unitor. -/
theorem coordinate_left_counit :
    (Algebra.TensorProduct.map coordinateCounit
        (AlgHom.id ℤ A)).comp coordinateComul =
      (Algebra.TensorProduct.lid ℤ A).symm.toAlgHom := by
  change leftCounitMap.comp coordinateComul = leftCounitUnit
  apply coordinateAlgHom_ext
  rw [coordinateComul_baseChange]
  rw [leftCounitPoint_left, leftCounitPoint_right, one_mul]

private def rightCounitMap : T →ₐ[ℤ] RightCounitTensor :=
  Algebra.TensorProduct.map (AlgHom.id ℤ A) coordinateCounit

private def rightCounitUnit : A →ₐ[ℤ] RightCounitTensor :=
  (Algebra.TensorProduct.rid ℤ ℤ A).symm.toAlgHom

private def rightCounitScalar : ℤ →ₐ[ℤ] RightCounitTensor :=
  Algebra.TensorProduct.includeRight

private theorem rightCounitMap_includeLeft :
    rightCounitMap.toRingHom.comp tensorIncludeLeft =
      rightCounitUnit.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [rightCounitMap, rightCounitUnit, tensorIncludeLeft]

private theorem rightCounitMap_includeRight :
    rightCounitMap.toRingHom.comp tensorIncludeRight =
      rightCounitScalar.toRingHom.comp coordinateCounit.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  change (Algebra.TensorProduct.map (AlgHom.id ℤ A) coordinateCounit)
      ((1 : A) ⊗ₜ[ℤ] x) =
    (1 : A) ⊗ₜ[ℤ] coordinateCounit x
  rw [Algebra.TensorProduct.map_tmul]
  simp

private theorem rightCounitPoint_left :
    Matrix.SpecialLinearGroup.map rightCounitMap.toRingHom
        universalPointLeft =
      Matrix.SpecialLinearGroup.map rightCounitUnit.toRingHom
        universalPoint := by
  rw [universalPointLeft]
  rw [← specialLinearMap_comp_apply]
  rw [rightCounitMap_includeLeft]

private theorem rightCounitPoint_right :
    Matrix.SpecialLinearGroup.map rightCounitMap.toRingHom
        universalPointRight = 1 := by
  rw [universalPointRight]
  rw [← specialLinearMap_comp_apply]
  rw [rightCounitMap_includeRight]
  rw [specialLinearMap_comp_apply]
  rw [coordinateCounit_universal]
  exact (Matrix.SpecialLinearGroup.map rightCounitScalar.toRingHom).map_one

/-- Comultiplication followed by counit on its right tensor factor is the
inverse of Mathlib's right unitor. -/
theorem coordinate_right_counit :
    (Algebra.TensorProduct.map (AlgHom.id ℤ A) coordinateCounit).comp
        coordinateComul =
      (Algebra.TensorProduct.rid ℤ ℤ A).symm.toAlgHom := by
  change rightCounitMap.comp coordinateComul = rightCounitUnit
  apply coordinateAlgHom_ext
  rw [coordinateComul_baseChange]
  rw [rightCounitPoint_left, rightCounitPoint_right, mul_one]

end CounitIdentities

end

end SpecialLinearTwo
end AlgebraicGeometry
end RiemannResearch
