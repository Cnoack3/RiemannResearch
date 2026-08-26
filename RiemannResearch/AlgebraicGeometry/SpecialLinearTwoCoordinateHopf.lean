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

private theorem coordinate_commute (x y : A) : Commute x y := by
  change x * y = y * x
  exact @mul_comm A (inferInstance : CommMagma A) _ _

private def antipodeLeftMap : T →ₐ[ℤ] A :=
  Algebra.TensorProduct.lift coordinateAntipode (AlgHom.id ℤ A)
    (fun x y => coordinate_commute
      (coordinateAntipode x) ((AlgHom.id ℤ A) y))

private def antipodeRightMap : T →ₐ[ℤ] A :=
  Algebra.TensorProduct.lift (AlgHom.id ℤ A) coordinateAntipode
    (fun x y => coordinate_commute
      ((AlgHom.id ℤ A) x) (coordinateAntipode y))

private theorem antipodeLeftMap_includeLeft :
    antipodeLeftMap.toRingHom.comp tensorIncludeLeft =
      coordinateAntipode.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  change coordinateAntipode x * 1 = coordinateAntipode x
  exact @mul_one A (inferInstance : MulOneClass A) _

private theorem antipodeLeftMap_includeRight :
    antipodeLeftMap.toRingHom.comp tensorIncludeRight =
      (AlgHom.id ℤ A).toRingHom := by
  apply DFunLike.ext _ _
  intro x
  change (Algebra.TensorProduct.lift coordinateAntipode (AlgHom.id ℤ A)
      (fun x y => coordinate_commute
        (coordinateAntipode x) ((AlgHom.id ℤ A) y)))
      ((1 : A) ⊗ₜ[ℤ] x) = x
  rw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, AlgHom.coe_id, id_eq]
  exact @one_mul A (inferInstance : MulOneClass A) x

private theorem antipodeRightMap_includeLeft :
    antipodeRightMap.toRingHom.comp tensorIncludeLeft =
      (AlgHom.id ℤ A).toRingHom := by
  apply DFunLike.ext _ _
  intro x
  change (Algebra.TensorProduct.lift (AlgHom.id ℤ A) coordinateAntipode
      (fun x y => coordinate_commute
        ((AlgHom.id ℤ A) x) (coordinateAntipode y)))
      (x ⊗ₜ[ℤ] (1 : A)) = x
  rw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, AlgHom.coe_id, id_eq]
  exact @mul_one A (inferInstance : MulOneClass A) x

private theorem antipodeRightMap_includeRight :
    antipodeRightMap.toRingHom.comp tensorIncludeRight =
      coordinateAntipode.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  change 1 * coordinateAntipode x = coordinateAntipode x
  exact @one_mul A (inferInstance : MulOneClass A) _

private theorem antipodeLeftPoint_left :
    Matrix.SpecialLinearGroup.map antipodeLeftMap.toRingHom
        universalPointLeft = universalPoint⁻¹ := by
  rw [universalPointLeft]
  rw [← specialLinearMap_comp_apply]
  rw [antipodeLeftMap_includeLeft]
  exact coordinateAntipode_universal

private theorem antipodeLeftPoint_right :
    Matrix.SpecialLinearGroup.map antipodeLeftMap.toRingHom
        universalPointRight = universalPoint := by
  rw [universalPointRight]
  rw [← specialLinearMap_comp_apply]
  rw [antipodeLeftMap_includeRight]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

private theorem antipodeRightPoint_left :
    Matrix.SpecialLinearGroup.map antipodeRightMap.toRingHom
        universalPointLeft = universalPoint := by
  rw [universalPointLeft]
  rw [← specialLinearMap_comp_apply]
  rw [antipodeRightMap_includeLeft]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

private theorem antipodeRightPoint_right :
    Matrix.SpecialLinearGroup.map antipodeRightMap.toRingHom
        universalPointRight = universalPoint⁻¹ := by
  rw [universalPointRight]
  rw [← specialLinearMap_comp_apply]
  rw [antipodeRightMap_includeRight]
  exact coordinateAntipode_universal

private theorem antipodeUnitPoint :
    Matrix.SpecialLinearGroup.map
        (((Algebra.ofId ℤ A).comp coordinateCounit).toRingHom)
        universalPoint = 1 := by
  change Matrix.SpecialLinearGroup.map
      ((algebraMap ℤ A).comp coordinateCounit.toRingHom)
      universalPoint = 1
  rw [specialLinearMap_comp_apply]
  rw [coordinateCounit_universal]
  exact map_one _

private theorem antipodeLeft_identity :
    antipodeLeftMap.comp coordinateComul =
      (Algebra.ofId ℤ A).comp coordinateCounit := by
  apply coordinateAlgHom_ext (R := A)
  rw [coordinateComul_baseChange (R := A)]
  rw [antipodeLeftPoint_left, antipodeLeftPoint_right,
    inv_mul_cancel, antipodeUnitPoint]

private theorem antipodeRight_identity :
    antipodeRightMap.comp coordinateComul =
      (Algebra.ofId ℤ A).comp coordinateCounit := by
  apply coordinateAlgHom_ext (R := A)
  rw [coordinateComul_baseChange (R := A)]
  rw [antipodeRightPoint_left, antipodeRightPoint_right,
    mul_inv_cancel, antipodeUnitPoint]

/-- The coordinate antipode is a left inverse of the identity under the
coordinate convolution product. -/
theorem coordinateAntipode_left :
    (Algebra.TensorProduct.lift coordinateAntipode (AlgHom.id ℤ A)
        (fun x y => coordinate_commute
          (coordinateAntipode x) ((AlgHom.id ℤ A) y))).comp
        coordinateComul =
      (Algebra.ofId ℤ A).comp coordinateCounit := by
  exact antipodeLeft_identity

/-- The coordinate antipode is a right inverse of the identity under the
coordinate convolution product. -/
theorem coordinateAntipode_right :
    (Algebra.TensorProduct.lift (AlgHom.id ℤ A) coordinateAntipode
        (fun x y => coordinate_commute
          ((AlgHom.id ℤ A) x) (coordinateAntipode y))).comp
        coordinateComul =
      (Algebra.ofId ℤ A).comp coordinateCounit := by
  exact antipodeRight_identity


local instance hopfTensorAddCommMonoid : AddCommMonoid T :=
  (inferInstance : Semiring T).toAddCommMonoid

local instance hopfTensorIntModule : Module ℤ T :=
  @Algebra.toModule ℤ T _ _ (inferInstance : Algebra ℤ T)

private abbrev LeftTripleTensor := T ⊗[ℤ] A
private abbrev RightTripleTensor := A ⊗[ℤ] T

noncomputable local instance leftTripleTensorRing :
    Ring LeftTripleTensor := by
  let sr : Semiring LeftTripleTensor := inferInstance
  let ag : AddCommGroup LeftTripleTensor := inferInstance
  exact { sr, ag with
    sub_eq_add_neg := by intros; rfl
    intCast := Int.castDef
    intCast_ofNat := by intro n; rfl
    intCast_negSucc := by intro n; rfl }

noncomputable local instance leftTripleTensorCommRing :
    CommRing LeftTripleTensor := by
  let cr : CommSemiring LeftTripleTensor :=
    @Algebra.TensorProduct.instCommSemiring ℤ T A
      (inferInstance : CommSemiring ℤ)
      (inferInstance : CommSemiring T)
      (inferInstance : Algebra ℤ T)
      (inferInstance : CommSemiring A)
      (inferInstance : Algebra ℤ A)
  exact { leftTripleTensorRing, cr with }

local instance leftTripleTensorAlgebra : Algebra ℤ LeftTripleTensor :=
  @Algebra.TensorProduct.instAlgebra ℤ T A
    (inferInstance : CommSemiring ℤ)
    (inferInstance : Semiring T)
    (inferInstance : Algebra ℤ T)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)

noncomputable local instance rightTripleTensorRing :
    Ring RightTripleTensor := by
  let sr : Semiring RightTripleTensor := inferInstance
  let ag : AddCommGroup RightTripleTensor := inferInstance
  exact { sr, ag with
    sub_eq_add_neg := by intros; rfl
    intCast := Int.castDef
    intCast_ofNat := by intro n; rfl
    intCast_negSucc := by intro n; rfl }

noncomputable local instance rightTripleTensorCommRing :
    CommRing RightTripleTensor := by
  let cr : CommSemiring RightTripleTensor :=
    @Algebra.TensorProduct.instCommSemiring ℤ A T
      (inferInstance : CommSemiring ℤ)
      (inferInstance : CommSemiring A)
      (inferInstance : Algebra ℤ A)
      (inferInstance : CommSemiring T)
      (inferInstance : Algebra ℤ T)
  exact { rightTripleTensorRing, cr with }

local instance rightTripleTensorAlgebra : Algebra ℤ RightTripleTensor :=
  @Algebra.TensorProduct.instAlgebra ℤ A T
    (inferInstance : CommSemiring ℤ)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)
    (inferInstance : Semiring T)
    (inferInstance : Algebra ℤ T)

private def coassocLeftOuter : T →ₐ[ℤ] RightTripleTensor :=
  (Algebra.TensorProduct.assoc ℤ ℤ ℤ A A A).toAlgHom.comp
    (Algebra.TensorProduct.map coordinateComul (AlgHom.id ℤ A))

private def coassocRightOuter : T →ₐ[ℤ] RightTripleTensor :=
  Algebra.TensorProduct.map (AlgHom.id ℤ A) coordinateComul

private def coassocPair12 : T →ₐ[ℤ] RightTripleTensor :=
  (Algebra.TensorProduct.assoc ℤ ℤ ℤ A A A).toAlgHom.comp
    (Algebra.TensorProduct.includeLeft : T →ₐ[ℤ] LeftTripleTensor)

private def coassocPoint3 : A →ₐ[ℤ] RightTripleTensor :=
  (Algebra.TensorProduct.assoc ℤ ℤ ℤ A A A).toAlgHom.comp
    (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] LeftTripleTensor)

private def coassocPoint1 : A →ₐ[ℤ] RightTripleTensor :=
  (Algebra.TensorProduct.includeLeft : A →ₐ[ℤ] RightTripleTensor)

private def coassocPair23 : T →ₐ[ℤ] RightTripleTensor :=
  (Algebra.TensorProduct.includeRight : T →ₐ[ℤ] RightTripleTensor)

private theorem coassocLeftOuter_includeLeft :
    coassocLeftOuter.toRingHom.comp tensorIncludeLeft =
      coassocPair12.toRingHom.comp coordinateComul.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [coassocLeftOuter, coassocPair12, tensorIncludeLeft]

private theorem coassocLeftOuter_includeRight :
    coassocLeftOuter.toRingHom.comp tensorIncludeRight =
      coassocPoint3.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [coassocLeftOuter, coassocPoint3, tensorIncludeRight]

private theorem coassocRightOuter_includeLeft :
    coassocRightOuter.toRingHom.comp tensorIncludeLeft =
      coassocPoint1.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [coassocRightOuter, coassocPoint1, tensorIncludeLeft]

private theorem coassocRightOuter_includeRight :
    coassocRightOuter.toRingHom.comp tensorIncludeRight =
      coassocPair23.toRingHom.comp coordinateComul.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [coassocRightOuter, coassocPair23, tensorIncludeRight]

private theorem coassocPair12_includeLeft :
    coassocPair12.toRingHom.comp tensorIncludeLeft =
      coassocPoint1.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp,
    RingHom.coe_coe, Function.comp_apply]
  change x ⊗ₜ[ℤ] ((1 : A) ⊗ₜ[ℤ] (1 : A)) =
    x ⊗ₜ[ℤ] (1 : T)
  exact (congrArg (fun z : T => x ⊗ₜ[ℤ] z)
    (Algebra.TensorProduct.one_def :
      (1 : T) = (1 : A) ⊗ₜ[ℤ] (1 : A))).symm

private theorem coassocMiddleFactors :
    coassocPair12.toRingHom.comp tensorIncludeRight =
      coassocPair23.toRingHom.comp tensorIncludeLeft := by
  apply DFunLike.ext _ _
  intro x
  simp [coassocPair12, coassocPair23,
    tensorIncludeLeft, tensorIncludeRight]

private theorem coassocPair23_includeRight :
    coassocPair23.toRingHom.comp tensorIncludeRight =
      coassocPoint3.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp,
    RingHom.coe_coe, Function.comp_apply]
  change (1 : A) ⊗ₜ[ℤ] ((1 : A) ⊗ₜ[ℤ] x) =
    (Algebra.TensorProduct.assoc ℤ ℤ ℤ A A A)
      ((1 : T) ⊗ₜ[ℤ] x)
  rw [show (1 : T) = (1 : A) ⊗ₜ[ℤ] (1 : A) from
    Algebra.TensorProduct.one_def]
  rfl


private theorem coassocLeftPoint_left :
    Matrix.SpecialLinearGroup.map coassocLeftOuter.toRingHom
        universalPointLeft =
      Matrix.SpecialLinearGroup.map coassocPair12.toRingHom
          universalPointLeft *
        Matrix.SpecialLinearGroup.map coassocPair12.toRingHom
          universalPointRight := by
  rw [universalPointLeft]
  rw [← specialLinearMap_comp_apply]
  rw [coassocLeftOuter_includeLeft]
  exact coordinateComul_baseChange coassocPair12

private theorem coassocLeftPoint_right :
    Matrix.SpecialLinearGroup.map coassocLeftOuter.toRingHom
        universalPointRight =
      Matrix.SpecialLinearGroup.map coassocPoint3.toRingHom
        universalPoint := by
  rw [universalPointRight]
  rw [← specialLinearMap_comp_apply]
  rw [coassocLeftOuter_includeRight]

private theorem coassocRightPoint_left :
    Matrix.SpecialLinearGroup.map coassocRightOuter.toRingHom
        universalPointLeft =
      Matrix.SpecialLinearGroup.map coassocPoint1.toRingHom
        universalPoint := by
  rw [universalPointLeft]
  rw [← specialLinearMap_comp_apply]
  rw [coassocRightOuter_includeLeft]

private theorem coassocRightPoint_right :
    Matrix.SpecialLinearGroup.map coassocRightOuter.toRingHom
        universalPointRight =
      Matrix.SpecialLinearGroup.map coassocPair23.toRingHom
          universalPointLeft *
        Matrix.SpecialLinearGroup.map coassocPair23.toRingHom
          universalPointRight := by
  rw [universalPointRight]
  rw [← specialLinearMap_comp_apply]
  rw [coassocRightOuter_includeRight]
  exact coordinateComul_baseChange coassocPair23

private theorem coassocPair12Point_left :
    Matrix.SpecialLinearGroup.map coassocPair12.toRingHom
        universalPointLeft =
      Matrix.SpecialLinearGroup.map coassocPoint1.toRingHom
        universalPoint := by
  rw [universalPointLeft]
  rw [← specialLinearMap_comp_apply]
  rw [coassocPair12_includeLeft]

private theorem coassocMiddlePoints :
    Matrix.SpecialLinearGroup.map coassocPair12.toRingHom
        universalPointRight =
      Matrix.SpecialLinearGroup.map coassocPair23.toRingHom
        universalPointLeft := by
  rw [universalPointRight, universalPointLeft]
  rw [← specialLinearMap_comp_apply,
    ← specialLinearMap_comp_apply]
  rw [coassocMiddleFactors]

private theorem coassocPair23Point_right :
    Matrix.SpecialLinearGroup.map coassocPair23.toRingHom
        universalPointRight =
      Matrix.SpecialLinearGroup.map coassocPoint3.toRingHom
        universalPoint := by
  rw [universalPointRight]
  rw [← specialLinearMap_comp_apply]
  rw [coassocPair23_includeRight]

/-- Coassociativity of the integral `SL₂` coordinate comultiplication. -/
theorem coordinate_coassoc :
    (Algebra.TensorProduct.assoc ℤ ℤ ℤ A A A).toAlgHom.comp
          ((Algebra.TensorProduct.map coordinateComul
            (AlgHom.id ℤ A)).comp coordinateComul) =
      (Algebra.TensorProduct.map (AlgHom.id ℤ A)
          coordinateComul).comp coordinateComul := by
  change coassocLeftOuter.comp coordinateComul =
    coassocRightOuter.comp coordinateComul
  apply coordinateAlgHom_ext
  rw [coordinateComul_baseChange, coordinateComul_baseChange]
  rw [coassocLeftPoint_left, coassocLeftPoint_right,
    coassocRightPoint_left, coassocRightPoint_right,
    coassocPair12Point_left, coassocMiddlePoints,
    coassocPair23Point_right]
  exact mul_assoc _ _ _


/-- The integral coordinate algebra of split `SL₂` is a bialgebra. -/
@[instance_reducible] noncomputable instance coordinateBialgebra :
    Bialgebra ℤ A :=
  Bialgebra.ofAlgHom coordinateComul coordinateCounit
    coordinate_coassoc coordinate_left_counit coordinate_right_counit

private theorem coordinateAntipode_left_installed :
    (Algebra.TensorProduct.lift coordinateAntipode
        (AlgHom.id ℤ A)
        (fun x => Commute.all (coordinateAntipode x))).comp
      (Bialgebra.comulAlgHom ℤ A) =
        (Algebra.ofId ℤ A).comp (Bialgebra.counitAlgHom ℤ A) := by
  change
    (Algebra.TensorProduct.lift coordinateAntipode
        (AlgHom.id ℤ A)
        (fun x => Commute.all (coordinateAntipode x))).comp
      coordinateComul =
        (Algebra.ofId ℤ A).comp coordinateCounit
  exact coordinateAntipode_left

private theorem coordinateAntipode_right_installed :
    (Algebra.TensorProduct.lift (AlgHom.id ℤ A)
        coordinateAntipode
        (fun x y => Commute.all
          ((AlgHom.id ℤ A) x) (coordinateAntipode y))).comp
      (Bialgebra.comulAlgHom ℤ A) =
        (Algebra.ofId ℤ A).comp (Bialgebra.counitAlgHom ℤ A) := by
  change
    (Algebra.TensorProduct.lift (AlgHom.id ℤ A)
        coordinateAntipode
        (fun x y => Commute.all
          ((AlgHom.id ℤ A) x) (coordinateAntipode y))).comp
      coordinateComul =
        (Algebra.ofId ℤ A).comp coordinateCounit
  exact coordinateAntipode_right

private theorem antipodeLeftLinearBridge (z : T) :
    (LinearMap.mul' ℤ A)
        ((TensorProduct.map coordinateAntipode.toLinearMap
          (LinearMap.id : A →ₗ[ℤ] A)) z) =
      (Algebra.TensorProduct.lift coordinateAntipode
        (AlgHom.id ℤ A)
        (fun x => Commute.all (coordinateAntipode x))) z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  · intro x y hx hy
    simp [hx, hy]

private theorem antipodeRightLinearBridge (z : T) :
    (LinearMap.mul' ℤ A)
        ((TensorProduct.map (LinearMap.id : A →ₗ[ℤ] A)
          coordinateAntipode.toLinearMap) z) =
      (Algebra.TensorProduct.lift (AlgHom.id ℤ A)
        coordinateAntipode
        (fun x y => Commute.all
          ((AlgHom.id ℤ A) x) (coordinateAntipode y))) z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  · intro x y hx hy
    simp [hx, hy]

private theorem coordinateAntipode_left_conv :
    WithConv.toConv coordinateAntipode.toLinearMap *
        WithConv.toConv (LinearMap.id : A →ₗ[ℤ] A) = 1 := by
  apply WithConv.ext
  change
    (LinearMap.mul' ℤ A) ∘ₗ
          (TensorProduct.map coordinateAntipode.toLinearMap
            (LinearMap.id : A →ₗ[ℤ] A)) ∘ₗ
          CoalgebraStruct.comul =
      (Algebra.linearMap ℤ A) ∘ₗ CoalgebraStruct.counit
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [antipodeLeftLinearBridge]
  exact DFunLike.congr_fun coordinateAntipode_left_installed x

private theorem coordinateAntipode_right_conv :
    WithConv.toConv (LinearMap.id : A →ₗ[ℤ] A) *
        WithConv.toConv coordinateAntipode.toLinearMap = 1 := by
  apply WithConv.ext
  change
    (LinearMap.mul' ℤ A) ∘ₗ
          (TensorProduct.map (LinearMap.id : A →ₗ[ℤ] A)
            coordinateAntipode.toLinearMap) ∘ₗ
          CoalgebraStruct.comul =
      (Algebra.linearMap ℤ A) ∘ₗ CoalgebraStruct.counit
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [antipodeRightLinearBridge]
  exact DFunLike.congr_fun coordinateAntipode_right_installed x

/-- The integral coordinate algebra of split `SL₂` is a Hopf algebra. -/
@[instance_reducible] noncomputable instance coordinateHopfAlgebra :
    HopfAlgebra ℤ A :=
  HopfAlgebra.ofConvInverse coordinateAntipode.toLinearMap
    coordinateAntipode_left_conv coordinateAntipode_right_conv

end

end SpecialLinearTwo
end AlgebraicGeometry
end RiemannResearch
