/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateCogroup

/-!
# Transport lemmas toward the split-Zorn coordinate Hopf algebra

This module transports the group laws on coefficient-related triples through
the explicit coordinate-ring universal property.  It proves the two counit
identities against Mathlib's exact unitors, coassociativity against its tensor
associator, and both antipode identities.  These five identities install the
canonical integral `Bialgebra` and `HopfAlgebra` instances.

The construction is made for the canonical small integral coordinate ring
`RelatedTripleCoordinateRing.{0}`.  This is the object needed by Mathlib's
commutative-Hopf and affine-group-scheme categories.  The current coordinate
evaluation API is same-universe, so this module does not assert a
universe-polymorphic counit from `RelatedTripleCoordinateRing.{u}` to `ℤ`.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

noncomputable section

open scoped TensorProduct

private abbrev A := RelatedTripleCoordinateRing.{0}

local instance relatedTripleHopfCoordinateAddCommMonoid : AddCommMonoid A :=
  (inferInstance : Semiring A).toAddCommMonoid

local instance relatedTripleHopfCoordinateIntModule : Module ℤ A :=
  @Algebra.toModule ℤ A _ _
    (inferInstance : Algebra ℤ A)

private abbrev T := A ⊗[ℤ] A

noncomputable local instance : Ring T :=
  relatedTripleTensorProductRing

noncomputable local instance : CommRing T :=
  relatedTripleTensorProductCommRing

local instance relatedTripleHopfTensorIntAlgebra : Algebra ℤ T :=
  @Algebra.TensorProduct.instAlgebra ℤ A A
    (inferInstance : CommSemiring ℤ)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)

/-- Two algebra maps out of the coordinate ring are equal when they carry the
universal related triple to the same point. -/
theorem relatedTripleCoordinateAlgHom_ext
    {R : Type} [CommRing R] [Algebra ℤ R]
    (f g : A →ₐ[ℤ] R)
    (h :
      coefficientRelatedTripleBaseChange f.toRingHom
          universalCoefficientRelatedTriple =
        coefficientRelatedTripleBaseChange g.toRingHom
          universalCoefficientRelatedTriple) :
    f = g := by
  apply AlgHom.ext
  intro x
  have he : f.toRingHom = g.toRingHom := by
    rw [← relatedTripleCoordinateEvaluation_baseChange f.toRingHom,
      ← relatedTripleCoordinateEvaluation_baseChange g.toRingHom, h]
  exact DFunLike.congr_fun he x

/-- Pointwise form of functoriality of coefficient base change. -/
theorem coefficientRelatedTripleBaseChange_comp_apply
    {R S U : Type} [CommRing R] [CommRing S] [CommRing U]
    (f : R →+* S) (g : S →+* U)
    (x : coefficientRelatedTripleGroup R) :
    coefficientRelatedTripleBaseChange (g.comp f) x =
      coefficientRelatedTripleBaseChange g
        (coefficientRelatedTripleBaseChange f x) :=
  DFunLike.congr_fun (coefficientRelatedTripleBaseChange_comp f g) x

/-- Evaluation after comultiplication is multiplication of the two points
obtained from the tensor factors. -/
theorem relatedTripleCoordinateComul_baseChange
    {R : Type} [CommRing R] [Algebra ℤ R]
    (f : T →ₐ[ℤ] R) :
    coefficientRelatedTripleBaseChange
        ((f.comp relatedTripleCoordinateComul).toRingHom)
        universalCoefficientRelatedTriple =
      coefficientRelatedTripleBaseChange f.toRingHom
          universalCoefficientRelatedTripleLeft *
        coefficientRelatedTripleBaseChange f.toRingHom
          universalCoefficientRelatedTripleRight := by
  change coefficientRelatedTripleBaseChange
      (f.toRingHom.comp relatedTripleCoordinateComul.toRingHom)
      universalCoefficientRelatedTriple = _
  rw [coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoordinateComul_universal]
  exact (coefficientRelatedTripleBaseChange f.toRingHom).map_mul _ _

/-- Evaluation after the counit is the identity point. -/
theorem relatedTripleCoordinateCounit_baseChange
    {R : Type} [CommRing R] [Algebra ℤ R]
    (f : ℤ →ₐ[ℤ] R) :
    coefficientRelatedTripleBaseChange
        ((f.comp relatedTripleCoordinateCounit).toRingHom)
        universalCoefficientRelatedTriple = 1 := by
  change coefficientRelatedTripleBaseChange
      (f.toRingHom.comp relatedTripleCoordinateCounit.toRingHom)
      universalCoefficientRelatedTriple = 1
  rw [coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoordinateCounit_universal]
  exact map_one _

section CounitIdentities

local instance relatedTripleHopfIntAddCommMonoid : AddCommMonoid ℤ :=
  (inferInstance : Semiring ℤ).toAddCommMonoid

local instance relatedTripleHopfIntModule : Module ℤ ℤ :=
  @Algebra.toModule ℤ ℤ _ _
    (inferInstance : Algebra ℤ ℤ)

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

private def relatedTripleLeftCounitMap :
    T →ₐ[ℤ] LeftCounitTensor :=
  Algebra.TensorProduct.map relatedTripleCoordinateCounit
    (AlgHom.id ℤ A)

private def relatedTripleLeftCounitUnit :
    A →ₐ[ℤ] LeftCounitTensor :=
  (Algebra.TensorProduct.lid ℤ A).symm.toAlgHom

private def relatedTripleLeftCounitScalar :
    ℤ →ₐ[ℤ] LeftCounitTensor :=
  Algebra.TensorProduct.includeLeft

private theorem relatedTripleLeftCounitMap_includeLeft :
    relatedTripleLeftCounitMap.toRingHom.comp
        relatedTripleTensorIncludeLeft =
      relatedTripleLeftCounitScalar.toRingHom.comp
        relatedTripleCoordinateCounit.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [relatedTripleLeftCounitMap,
    relatedTripleLeftCounitScalar,
    relatedTripleTensorIncludeLeft]

private theorem relatedTripleLeftCounitMap_includeRight :
    relatedTripleLeftCounitMap.toRingHom.comp
        relatedTripleTensorIncludeRight =
      relatedTripleLeftCounitUnit.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [relatedTripleLeftCounitMap,
    relatedTripleLeftCounitUnit,
    relatedTripleTensorIncludeRight]

private theorem relatedTripleLeftCounitPoint_left :
    coefficientRelatedTripleBaseChange
        relatedTripleLeftCounitMap.toRingHom
        universalCoefficientRelatedTripleLeft = 1 := by
  rw [universalCoefficientRelatedTripleLeft]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleLeftCounitMap_includeLeft]
  rw [coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoordinateCounit_universal]
  exact
    (coefficientRelatedTripleBaseChange
      relatedTripleLeftCounitScalar.toRingHom).map_one

private theorem relatedTripleLeftCounitPoint_right :
    coefficientRelatedTripleBaseChange
        relatedTripleLeftCounitMap.toRingHom
        universalCoefficientRelatedTripleRight =
      coefficientRelatedTripleBaseChange
        relatedTripleLeftCounitUnit.toRingHom
        universalCoefficientRelatedTriple := by
  rw [universalCoefficientRelatedTripleRight]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleLeftCounitMap_includeRight]

/-- The coordinate comultiplication followed by counit on its left tensor
factor is the inverse of Mathlib's left unitor. -/
theorem relatedTripleCoordinate_left_counit :
    (Algebra.TensorProduct.map relatedTripleCoordinateCounit
        (AlgHom.id ℤ A)).comp relatedTripleCoordinateComul =
      (Algebra.TensorProduct.lid ℤ A).symm.toAlgHom := by
  change relatedTripleLeftCounitMap.comp
      relatedTripleCoordinateComul =
    relatedTripleLeftCounitUnit
  apply relatedTripleCoordinateAlgHom_ext
  rw [relatedTripleCoordinateComul_baseChange]
  rw [relatedTripleLeftCounitPoint_left,
    relatedTripleLeftCounitPoint_right, one_mul]

private def relatedTripleRightCounitMap :
    T →ₐ[ℤ] RightCounitTensor :=
  Algebra.TensorProduct.map (AlgHom.id ℤ A)
    relatedTripleCoordinateCounit

private def relatedTripleRightCounitUnit :
    A →ₐ[ℤ] RightCounitTensor :=
  (Algebra.TensorProduct.rid ℤ ℤ A).symm.toAlgHom

private def relatedTripleRightCounitScalar :
    ℤ →ₐ[ℤ] RightCounitTensor :=
  Algebra.TensorProduct.includeRight

private theorem relatedTripleRightCounitMap_includeLeft :
    relatedTripleRightCounitMap.toRingHom.comp
        relatedTripleTensorIncludeLeft =
      relatedTripleRightCounitUnit.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [relatedTripleRightCounitMap,
    relatedTripleRightCounitUnit,
    relatedTripleTensorIncludeLeft]

private theorem relatedTripleRightCounitMap_includeRight :
    relatedTripleRightCounitMap.toRingHom.comp
        relatedTripleTensorIncludeRight =
      relatedTripleRightCounitScalar.toRingHom.comp
        relatedTripleCoordinateCounit.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  change (Algebra.TensorProduct.map (AlgHom.id ℤ A)
      relatedTripleCoordinateCounit)
        ((1 : A) ⊗ₜ[ℤ] x) =
    (1 : A) ⊗ₜ[ℤ] relatedTripleCoordinateCounit x
  rw [Algebra.TensorProduct.map_tmul]
  simp

private theorem relatedTripleRightCounitPoint_left :
    coefficientRelatedTripleBaseChange
        relatedTripleRightCounitMap.toRingHom
        universalCoefficientRelatedTripleLeft =
      coefficientRelatedTripleBaseChange
        relatedTripleRightCounitUnit.toRingHom
        universalCoefficientRelatedTriple := by
  rw [universalCoefficientRelatedTripleLeft]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleRightCounitMap_includeLeft]

private theorem relatedTripleRightCounitPoint_right :
    coefficientRelatedTripleBaseChange
        relatedTripleRightCounitMap.toRingHom
        universalCoefficientRelatedTripleRight = 1 := by
  rw [universalCoefficientRelatedTripleRight]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleRightCounitMap_includeRight]
  rw [coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoordinateCounit_universal]
  exact
    (coefficientRelatedTripleBaseChange
      relatedTripleRightCounitScalar.toRingHom).map_one

/-- The coordinate comultiplication followed by counit on its right tensor
factor is the inverse of Mathlib's right unitor. -/
theorem relatedTripleCoordinate_right_counit :
    (Algebra.TensorProduct.map (AlgHom.id ℤ A)
        relatedTripleCoordinateCounit).comp
        relatedTripleCoordinateComul =
      (Algebra.TensorProduct.rid ℤ ℤ A).symm.toAlgHom := by
  change relatedTripleRightCounitMap.comp
      relatedTripleCoordinateComul =
    relatedTripleRightCounitUnit
  apply relatedTripleCoordinateAlgHom_ext
  rw [relatedTripleCoordinateComul_baseChange]
  rw [relatedTripleRightCounitPoint_left,
    relatedTripleRightCounitPoint_right, mul_one]

end CounitIdentities

private theorem relatedTripleCoordinate_commute (x y : A) :
    Commute x y := by
  change x * y = y * x
  exact @mul_comm A (inferInstance : CommMagma A) _ _

private def relatedTripleAntipodeLeftMap : T →ₐ[ℤ] A :=
  Algebra.TensorProduct.lift relatedTripleCoordinateAntipode
    (AlgHom.id ℤ A)
    (fun x y => relatedTripleCoordinate_commute
      (relatedTripleCoordinateAntipode x)
      ((AlgHom.id ℤ A) y))

private def relatedTripleAntipodeRightMap : T →ₐ[ℤ] A :=
  Algebra.TensorProduct.lift (AlgHom.id ℤ A)
    relatedTripleCoordinateAntipode
    (fun x y => relatedTripleCoordinate_commute
      ((AlgHom.id ℤ A) x)
      (relatedTripleCoordinateAntipode y))

private theorem relatedTripleAntipodeLeftMap_includeLeft :
    relatedTripleAntipodeLeftMap.toRingHom.comp
        relatedTripleTensorIncludeLeft =
      relatedTripleCoordinateAntipode.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  change relatedTripleCoordinateAntipode x * 1 =
    relatedTripleCoordinateAntipode x
  exact @mul_one A (inferInstance : MulOneClass A)
    (relatedTripleCoordinateAntipode x)

private theorem relatedTripleAntipodeLeftMap_includeRight :
    relatedTripleAntipodeLeftMap.toRingHom.comp
        relatedTripleTensorIncludeRight =
      (AlgHom.id ℤ A).toRingHom := by
  apply DFunLike.ext _ _
  intro x
  change
    (Algebra.TensorProduct.lift relatedTripleCoordinateAntipode
      (AlgHom.id ℤ A)
      (fun x y => relatedTripleCoordinate_commute
        (relatedTripleCoordinateAntipode x)
        ((AlgHom.id ℤ A) y))) ((1 : A) ⊗ₜ[ℤ] x) = x
  rw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, AlgHom.coe_id, id_eq]
  exact @one_mul A (inferInstance : MulOneClass A) x

private theorem relatedTripleAntipodeRightMap_includeLeft :
    relatedTripleAntipodeRightMap.toRingHom.comp
        relatedTripleTensorIncludeLeft =
      (AlgHom.id ℤ A).toRingHom := by
  apply DFunLike.ext _ _
  intro x
  change
    (Algebra.TensorProduct.lift (AlgHom.id ℤ A)
      relatedTripleCoordinateAntipode
      (fun x y => relatedTripleCoordinate_commute
        ((AlgHom.id ℤ A) x)
        (relatedTripleCoordinateAntipode y))) (x ⊗ₜ[ℤ] (1 : A)) = x
  rw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, AlgHom.coe_id, id_eq]
  exact @mul_one A (inferInstance : MulOneClass A) x

private theorem relatedTripleAntipodeRightMap_includeRight :
    relatedTripleAntipodeRightMap.toRingHom.comp
        relatedTripleTensorIncludeRight =
      relatedTripleCoordinateAntipode.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  change 1 * relatedTripleCoordinateAntipode x =
    relatedTripleCoordinateAntipode x
  exact @one_mul A (inferInstance : MulOneClass A)
    (relatedTripleCoordinateAntipode x)

private theorem relatedTripleAntipodeLeftPoint_left :
    coefficientRelatedTripleBaseChange
        relatedTripleAntipodeLeftMap.toRingHom
        universalCoefficientRelatedTripleLeft =
      universalCoefficientRelatedTriple⁻¹ := by
  rw [universalCoefficientRelatedTripleLeft]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleAntipodeLeftMap_includeLeft]
  exact relatedTripleCoordinateAntipode_universal

private theorem relatedTripleAntipodeLeftPoint_right :
    coefficientRelatedTripleBaseChange
        relatedTripleAntipodeLeftMap.toRingHom
        universalCoefficientRelatedTripleRight =
      universalCoefficientRelatedTriple := by
  rw [universalCoefficientRelatedTripleRight]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleAntipodeLeftMap_includeRight]
  change coefficientRelatedTripleBaseChange (RingHom.id A)
      universalCoefficientRelatedTriple =
    universalCoefficientRelatedTriple
  exact DFunLike.congr_fun
    coefficientRelatedTripleBaseChange_id
    universalCoefficientRelatedTriple

private theorem relatedTripleAntipodeRightPoint_left :
    coefficientRelatedTripleBaseChange
        relatedTripleAntipodeRightMap.toRingHom
        universalCoefficientRelatedTripleLeft =
      universalCoefficientRelatedTriple := by
  rw [universalCoefficientRelatedTripleLeft]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleAntipodeRightMap_includeLeft]
  change coefficientRelatedTripleBaseChange (RingHom.id A)
      universalCoefficientRelatedTriple =
    universalCoefficientRelatedTriple
  exact DFunLike.congr_fun
    coefficientRelatedTripleBaseChange_id
    universalCoefficientRelatedTriple

private theorem relatedTripleAntipodeRightPoint_right :
    coefficientRelatedTripleBaseChange
        relatedTripleAntipodeRightMap.toRingHom
        universalCoefficientRelatedTripleRight =
      universalCoefficientRelatedTriple⁻¹ := by
  rw [universalCoefficientRelatedTripleRight]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleAntipodeRightMap_includeRight]
  exact relatedTripleCoordinateAntipode_universal

private def relatedTripleEndoRepackage
    (f : A →ₐ[ℤ] A) :=
  relatedTripleCoordinateAlgHomOfRingHom (R := A)
    { toFun := fun x => f x
      map_one' := f.map_one
      map_mul' := fun x y => f.map_mul x y
      map_zero' := f.map_zero
      map_add' := fun x y => f.map_add x y }

private def relatedTripleTensorAlgHomOfRingHom
    {R : Type} [CommRing R] [Algebra ℤ R]
    (f : T →+* R) : T →ₐ[ℤ] R where
  toRingHom := f
  commutes' z := by simp

private def relatedTripleTensorRepackage
    (f : T →ₐ[ℤ] A) :=
  relatedTripleTensorAlgHomOfRingHom (R := A)
    { toFun := fun x => f x
      map_one' := f.map_one
      map_mul' := fun x y => f.map_mul x y
      map_zero' := f.map_zero
      map_add' := fun x y => f.map_add x y }

private def relatedTripleAntipodeLeftCompatible :=
  relatedTripleTensorRepackage relatedTripleAntipodeLeftMap

private def relatedTripleAntipodeRightCompatible :=
  relatedTripleTensorRepackage relatedTripleAntipodeRightMap

private def relatedTripleAntipodeUnitCompatible :=
  relatedTripleCoordinateAlgHomOfRingHom (R := A)
    ((algebraMap ℤ A).comp
      relatedTripleCoordinateCounit.toRingHom)

private theorem relatedTripleAntipodeLeftCompatiblePoint_left :
    coefficientRelatedTripleBaseChange
        relatedTripleAntipodeLeftCompatible.toRingHom
        universalCoefficientRelatedTripleLeft =
      universalCoefficientRelatedTriple⁻¹ := by
  change coefficientRelatedTripleBaseChange
      relatedTripleAntipodeLeftMap.toRingHom
      universalCoefficientRelatedTripleLeft =
    universalCoefficientRelatedTriple⁻¹
  exact relatedTripleAntipodeLeftPoint_left

private theorem relatedTripleAntipodeLeftCompatiblePoint_right :
    coefficientRelatedTripleBaseChange
        relatedTripleAntipodeLeftCompatible.toRingHom
        universalCoefficientRelatedTripleRight =
      universalCoefficientRelatedTriple := by
  change coefficientRelatedTripleBaseChange
      relatedTripleAntipodeLeftMap.toRingHom
      universalCoefficientRelatedTripleRight =
    universalCoefficientRelatedTriple
  exact relatedTripleAntipodeLeftPoint_right

private theorem relatedTripleAntipodeRightCompatiblePoint_left :
    coefficientRelatedTripleBaseChange
        relatedTripleAntipodeRightCompatible.toRingHom
        universalCoefficientRelatedTripleLeft =
      universalCoefficientRelatedTriple := by
  change coefficientRelatedTripleBaseChange
      relatedTripleAntipodeRightMap.toRingHom
      universalCoefficientRelatedTripleLeft =
    universalCoefficientRelatedTriple
  exact relatedTripleAntipodeRightPoint_left

private theorem relatedTripleAntipodeRightCompatiblePoint_right :
    coefficientRelatedTripleBaseChange
        relatedTripleAntipodeRightCompatible.toRingHom
        universalCoefficientRelatedTripleRight =
      universalCoefficientRelatedTriple⁻¹ := by
  change coefficientRelatedTripleBaseChange
      relatedTripleAntipodeRightMap.toRingHom
      universalCoefficientRelatedTripleRight =
    universalCoefficientRelatedTriple⁻¹
  exact relatedTripleAntipodeRightPoint_right

private theorem relatedTripleAntipodeUnitCompatiblePoint :
    coefficientRelatedTripleBaseChange
        relatedTripleAntipodeUnitCompatible.toRingHom
        universalCoefficientRelatedTriple = 1 := by
  change coefficientRelatedTripleBaseChange
      ((algebraMap ℤ A).comp
        relatedTripleCoordinateCounit.toRingHom)
      universalCoefficientRelatedTriple = 1
  rw [coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoordinateCounit_universal]
  exact map_one _

private theorem relatedTripleAntipodeLeftCompatible_identity :
    relatedTripleAntipodeLeftCompatible.comp
        relatedTripleCoordinateComul =
      relatedTripleAntipodeUnitCompatible := by
  apply relatedTripleCoordinateAlgHom_ext (R := A)
  rw [relatedTripleCoordinateComul_baseChange (R := A)]
  rw [relatedTripleAntipodeLeftCompatiblePoint_left,
    relatedTripleAntipodeLeftCompatiblePoint_right,
    inv_mul_cancel, relatedTripleAntipodeUnitCompatiblePoint]

private theorem relatedTripleAntipodeRightCompatible_identity :
    relatedTripleAntipodeRightCompatible.comp
        relatedTripleCoordinateComul =
      relatedTripleAntipodeUnitCompatible := by
  apply relatedTripleCoordinateAlgHom_ext (R := A)
  rw [relatedTripleCoordinateComul_baseChange (R := A)]
  rw [relatedTripleAntipodeRightCompatiblePoint_left,
    relatedTripleAntipodeRightCompatiblePoint_right,
    mul_inv_cancel, relatedTripleAntipodeUnitCompatiblePoint]

/-- The coordinate coinverse is a left convolution inverse of the identity. -/
theorem relatedTripleCoordinateAntipode_left :
    (Algebra.TensorProduct.lift relatedTripleCoordinateAntipode
        (AlgHom.id ℤ A)
        (fun x y => relatedTripleCoordinate_commute
          (relatedTripleCoordinateAntipode x)
          ((AlgHom.id ℤ A) y))).comp
        relatedTripleCoordinateComul =
      (Algebra.ofId ℤ A).comp relatedTripleCoordinateCounit := by
  apply AlgHom.ext
  intro x
  have hx := DFunLike.congr_fun
    relatedTripleAntipodeLeftCompatible_identity x
  exact hx

/-- The coordinate coinverse is a right convolution inverse of the identity. -/
theorem relatedTripleCoordinateAntipode_right :
    (Algebra.TensorProduct.lift (AlgHom.id ℤ A)
        relatedTripleCoordinateAntipode
        (fun x y => relatedTripleCoordinate_commute
          ((AlgHom.id ℤ A) x)
          (relatedTripleCoordinateAntipode y))).comp
        relatedTripleCoordinateComul =
      (Algebra.ofId ℤ A).comp relatedTripleCoordinateCounit := by
  apply AlgHom.ext
  intro x
  have hx := DFunLike.congr_fun
    relatedTripleAntipodeRightCompatible_identity x
  exact hx

local instance relatedTripleHopfTensorAddCommMonoid : AddCommMonoid T :=
  (inferInstance : Semiring T).toAddCommMonoid

local instance relatedTripleHopfTensorIntModule : Module ℤ T :=
  @Algebra.toModule ℤ T _ _
    (inferInstance : Algebra ℤ T)

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

local instance leftTripleTensorAlgebra :
    Algebra ℤ LeftTripleTensor :=
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

local instance rightTripleTensorAlgebra :
    Algebra ℤ RightTripleTensor :=
  @Algebra.TensorProduct.instAlgebra ℤ A T
    (inferInstance : CommSemiring ℤ)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)
    (inferInstance : Semiring T)
    (inferInstance : Algebra ℤ T)

private def relatedTripleCoassocLeftOuter :
    T →ₐ[ℤ] RightTripleTensor :=
  (Algebra.TensorProduct.assoc ℤ ℤ ℤ A A A).toAlgHom.comp
    (Algebra.TensorProduct.map relatedTripleCoordinateComul
      (AlgHom.id ℤ A))

private def relatedTripleCoassocRightOuter :
    T →ₐ[ℤ] RightTripleTensor :=
  Algebra.TensorProduct.map (AlgHom.id ℤ A)
    relatedTripleCoordinateComul

private def relatedTripleCoassocPair12 :
    T →ₐ[ℤ] RightTripleTensor :=
  (Algebra.TensorProduct.assoc ℤ ℤ ℤ A A A).toAlgHom.comp
    (Algebra.TensorProduct.includeLeft :
      T →ₐ[ℤ] LeftTripleTensor)

private def relatedTripleCoassocPoint3 :
    A →ₐ[ℤ] RightTripleTensor :=
  (Algebra.TensorProduct.assoc ℤ ℤ ℤ A A A).toAlgHom.comp
    (Algebra.TensorProduct.includeRight :
      A →ₐ[ℤ] LeftTripleTensor)

private def relatedTripleCoassocPoint1 :
    A →ₐ[ℤ] RightTripleTensor :=
  (Algebra.TensorProduct.includeLeft :
    A →ₐ[ℤ] RightTripleTensor)

private def relatedTripleCoassocPair23 :
    T →ₐ[ℤ] RightTripleTensor :=
  (Algebra.TensorProduct.includeRight :
    T →ₐ[ℤ] RightTripleTensor)

private theorem relatedTripleCoassocLeftOuter_includeLeft :
    relatedTripleCoassocLeftOuter.toRingHom.comp
        relatedTripleTensorIncludeLeft =
      relatedTripleCoassocPair12.toRingHom.comp
        relatedTripleCoordinateComul.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [relatedTripleCoassocLeftOuter, relatedTripleCoassocPair12,
    relatedTripleTensorIncludeLeft]

private theorem relatedTripleCoassocLeftOuter_includeRight :
    relatedTripleCoassocLeftOuter.toRingHom.comp
        relatedTripleTensorIncludeRight =
      relatedTripleCoassocPoint3.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [relatedTripleCoassocLeftOuter, relatedTripleCoassocPoint3,
    relatedTripleTensorIncludeRight]

private theorem relatedTripleCoassocRightOuter_includeLeft :
    relatedTripleCoassocRightOuter.toRingHom.comp
        relatedTripleTensorIncludeLeft =
      relatedTripleCoassocPoint1.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [relatedTripleCoassocRightOuter, relatedTripleCoassocPoint1,
    relatedTripleTensorIncludeLeft]

private theorem relatedTripleCoassocRightOuter_includeRight :
    relatedTripleCoassocRightOuter.toRingHom.comp
        relatedTripleTensorIncludeRight =
      relatedTripleCoassocPair23.toRingHom.comp
        relatedTripleCoordinateComul.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [relatedTripleCoassocRightOuter, relatedTripleCoassocPair23,
    relatedTripleTensorIncludeRight]

private theorem relatedTripleCoassocPair12_includeLeft :
    relatedTripleCoassocPair12.toRingHom.comp
        relatedTripleTensorIncludeLeft =
      relatedTripleCoassocPoint1.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp,
    RingHom.coe_coe, Function.comp_apply]
  change x ⊗ₜ[ℤ] ((1 : A) ⊗ₜ[ℤ] (1 : A)) =
    x ⊗ₜ[ℤ] (1 : T)
  exact
    (congrArg (fun z : T => x ⊗ₜ[ℤ] z)
      (Algebra.TensorProduct.one_def :
        (1 : T) = (1 : A) ⊗ₜ[ℤ] (1 : A))).symm

private theorem relatedTripleCoassocMiddleFactors :
    relatedTripleCoassocPair12.toRingHom.comp
        relatedTripleTensorIncludeRight =
      relatedTripleCoassocPair23.toRingHom.comp
        relatedTripleTensorIncludeLeft := by
  apply DFunLike.ext _ _
  intro x
  simp [relatedTripleCoassocPair12, relatedTripleCoassocPair23,
    relatedTripleTensorIncludeLeft, relatedTripleTensorIncludeRight]

private theorem relatedTripleCoassocPair23_includeRight :
    relatedTripleCoassocPair23.toRingHom.comp
        relatedTripleTensorIncludeRight =
      relatedTripleCoassocPoint3.toRingHom := by
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

private theorem relatedTripleCoassocLeftPoint_left :
    coefficientRelatedTripleBaseChange
        relatedTripleCoassocLeftOuter.toRingHom
        universalCoefficientRelatedTripleLeft =
      coefficientRelatedTripleBaseChange
          relatedTripleCoassocPair12.toRingHom
          universalCoefficientRelatedTripleLeft *
        coefficientRelatedTripleBaseChange
          relatedTripleCoassocPair12.toRingHom
          universalCoefficientRelatedTripleRight := by
  rw [universalCoefficientRelatedTripleLeft]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoassocLeftOuter_includeLeft]
  exact
    relatedTripleCoordinateComul_baseChange
      relatedTripleCoassocPair12

private theorem relatedTripleCoassocLeftPoint_right :
    coefficientRelatedTripleBaseChange
        relatedTripleCoassocLeftOuter.toRingHom
        universalCoefficientRelatedTripleRight =
      coefficientRelatedTripleBaseChange
        relatedTripleCoassocPoint3.toRingHom
        universalCoefficientRelatedTriple := by
  rw [universalCoefficientRelatedTripleRight]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoassocLeftOuter_includeRight]

private theorem relatedTripleCoassocRightPoint_left :
    coefficientRelatedTripleBaseChange
        relatedTripleCoassocRightOuter.toRingHom
        universalCoefficientRelatedTripleLeft =
      coefficientRelatedTripleBaseChange
        relatedTripleCoassocPoint1.toRingHom
        universalCoefficientRelatedTriple := by
  rw [universalCoefficientRelatedTripleLeft]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoassocRightOuter_includeLeft]

private theorem relatedTripleCoassocRightPoint_right :
    coefficientRelatedTripleBaseChange
        relatedTripleCoassocRightOuter.toRingHom
        universalCoefficientRelatedTripleRight =
      coefficientRelatedTripleBaseChange
          relatedTripleCoassocPair23.toRingHom
          universalCoefficientRelatedTripleLeft *
        coefficientRelatedTripleBaseChange
          relatedTripleCoassocPair23.toRingHom
          universalCoefficientRelatedTripleRight := by
  rw [universalCoefficientRelatedTripleRight]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoassocRightOuter_includeRight]
  exact
    relatedTripleCoordinateComul_baseChange
      relatedTripleCoassocPair23

private theorem relatedTripleCoassocPair12Point_left :
    coefficientRelatedTripleBaseChange
        relatedTripleCoassocPair12.toRingHom
        universalCoefficientRelatedTripleLeft =
      coefficientRelatedTripleBaseChange
        relatedTripleCoassocPoint1.toRingHom
        universalCoefficientRelatedTriple := by
  rw [universalCoefficientRelatedTripleLeft]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoassocPair12_includeLeft]

private theorem relatedTripleCoassocMiddlePoints :
    coefficientRelatedTripleBaseChange
        relatedTripleCoassocPair12.toRingHom
        universalCoefficientRelatedTripleRight =
      coefficientRelatedTripleBaseChange
        relatedTripleCoassocPair23.toRingHom
        universalCoefficientRelatedTripleLeft := by
  rw [universalCoefficientRelatedTripleRight,
    universalCoefficientRelatedTripleLeft]
  rw [← coefficientRelatedTripleBaseChange_comp_apply,
    ← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoassocMiddleFactors]

private theorem relatedTripleCoassocPair23Point_right :
    coefficientRelatedTripleBaseChange
        relatedTripleCoassocPair23.toRingHom
        universalCoefficientRelatedTripleRight =
      coefficientRelatedTripleBaseChange
        relatedTripleCoassocPoint3.toRingHom
        universalCoefficientRelatedTriple := by
  rw [universalCoefficientRelatedTripleRight]
  rw [← coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoassocPair23_includeRight]

/-- Coassociativity of the split-Zorn related-triple coordinate
comultiplication. -/
theorem relatedTripleCoordinate_coassoc :
    (Algebra.TensorProduct.assoc ℤ ℤ ℤ A A A).toAlgHom.comp
          ((Algebra.TensorProduct.map relatedTripleCoordinateComul
            (AlgHom.id ℤ A)).comp
            relatedTripleCoordinateComul) =
      (Algebra.TensorProduct.map (AlgHom.id ℤ A)
          relatedTripleCoordinateComul).comp
        relatedTripleCoordinateComul := by
  change relatedTripleCoassocLeftOuter.comp
      relatedTripleCoordinateComul =
    relatedTripleCoassocRightOuter.comp
      relatedTripleCoordinateComul
  apply relatedTripleCoordinateAlgHom_ext
  rw [relatedTripleCoordinateComul_baseChange,
    relatedTripleCoordinateComul_baseChange]
  rw [relatedTripleCoassocLeftPoint_left,
    relatedTripleCoassocLeftPoint_right,
    relatedTripleCoassocRightPoint_left,
    relatedTripleCoassocRightPoint_right,
    relatedTripleCoassocPair12Point_left,
    relatedTripleCoassocMiddlePoints,
    relatedTripleCoassocPair23Point_right]
  exact mul_assoc _ _ _

/-- The integral coordinate algebra of split-Zorn coefficient-related triples
is a bialgebra. -/
@[instance_reducible] noncomputable instance
    relatedTripleCoordinateBialgebra : Bialgebra ℤ A :=
  Bialgebra.ofAlgHom
    relatedTripleCoordinateComul
    relatedTripleCoordinateCounit
    relatedTripleCoordinate_coassoc
    relatedTripleCoordinate_left_counit
    relatedTripleCoordinate_right_counit

private theorem relatedTripleCoordinateAntipode_left_installed :
    (Algebra.TensorProduct.lift relatedTripleCoordinateAntipode
        (AlgHom.id ℤ A)
        (fun x => Commute.all
          (relatedTripleCoordinateAntipode x))).comp
        (Bialgebra.comulAlgHom ℤ A) =
      (Algebra.ofId ℤ A).comp
        (Bialgebra.counitAlgHom ℤ A) := by
  change
    (Algebra.TensorProduct.lift relatedTripleCoordinateAntipode
        (AlgHom.id ℤ A)
        (fun x => Commute.all
          (relatedTripleCoordinateAntipode x))).comp
        relatedTripleCoordinateComul =
      (Algebra.ofId ℤ A).comp relatedTripleCoordinateCounit
  exact relatedTripleCoordinateAntipode_left

private theorem relatedTripleCoordinateAntipode_right_installed :
    (Algebra.TensorProduct.lift (AlgHom.id ℤ A)
        relatedTripleCoordinateAntipode
        (fun x y => Commute.all
          ((AlgHom.id ℤ A) x)
          (relatedTripleCoordinateAntipode y))).comp
        (Bialgebra.comulAlgHom ℤ A) =
      (Algebra.ofId ℤ A).comp
        (Bialgebra.counitAlgHom ℤ A) := by
  change
    (Algebra.TensorProduct.lift (AlgHom.id ℤ A)
        relatedTripleCoordinateAntipode
        (fun x y => Commute.all
          ((AlgHom.id ℤ A) x)
          (relatedTripleCoordinateAntipode y))).comp
        relatedTripleCoordinateComul =
      (Algebra.ofId ℤ A).comp relatedTripleCoordinateCounit
  exact relatedTripleCoordinateAntipode_right


private theorem relatedTripleAntipodeLeftLinearBridge
    (z : T) :
    (LinearMap.mul' ℤ A)
        ((TensorProduct.map
          relatedTripleCoordinateAntipode.toLinearMap
          (LinearMap.id : A →ₗ[ℤ] A)) z) =
      (Algebra.TensorProduct.lift relatedTripleCoordinateAntipode
        (AlgHom.id ℤ A)
        (fun x => Commute.all
          (relatedTripleCoordinateAntipode x))) z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  · intro x y hx hy
    simp [hx, hy]

private theorem relatedTripleAntipodeRightLinearBridge
    (z : T) :
    (LinearMap.mul' ℤ A)
        ((TensorProduct.map
          (LinearMap.id : A →ₗ[ℤ] A)
          relatedTripleCoordinateAntipode.toLinearMap) z) =
      (Algebra.TensorProduct.lift (AlgHom.id ℤ A)
        relatedTripleCoordinateAntipode
        (fun x y => Commute.all
          ((AlgHom.id ℤ A) x)
          (relatedTripleCoordinateAntipode y))) z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  · intro x y hx hy
    simp [hx, hy]

private theorem relatedTripleCoordinateAntipode_left_conv :
    WithConv.toConv relatedTripleCoordinateAntipode.toLinearMap *
        WithConv.toConv (LinearMap.id : A →ₗ[ℤ] A) = 1 := by
  apply WithConv.ext
  change
    (LinearMap.mul' ℤ A) ∘ₗ
          (TensorProduct.map
            relatedTripleCoordinateAntipode.toLinearMap
            (LinearMap.id : A →ₗ[ℤ] A)) ∘ₗ
          CoalgebraStruct.comul =
      (Algebra.linearMap ℤ A) ∘ₗ CoalgebraStruct.counit
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [relatedTripleAntipodeLeftLinearBridge]
  exact DFunLike.congr_fun
    relatedTripleCoordinateAntipode_left_installed x

private theorem relatedTripleCoordinateAntipode_right_conv :
    WithConv.toConv (LinearMap.id : A →ₗ[ℤ] A) *
        WithConv.toConv relatedTripleCoordinateAntipode.toLinearMap = 1 := by
  apply WithConv.ext
  change
    (LinearMap.mul' ℤ A) ∘ₗ
          (TensorProduct.map
            (LinearMap.id : A →ₗ[ℤ] A)
            relatedTripleCoordinateAntipode.toLinearMap) ∘ₗ
          CoalgebraStruct.comul =
      (Algebra.linearMap ℤ A) ∘ₗ CoalgebraStruct.counit
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [relatedTripleAntipodeRightLinearBridge]
  exact DFunLike.congr_fun
    relatedTripleCoordinateAntipode_right_installed x

/-- The coordinate coinverse upgrades the bialgebra of split-Zorn
coefficient-related triples to a Hopf algebra. -/
@[instance_reducible] noncomputable instance
    relatedTripleCoordinateHopfAlgebra : HopfAlgebra ℤ A :=
  HopfAlgebra.ofConvInverse
    relatedTripleCoordinateAntipode.toLinearMap
    relatedTripleCoordinateAntipode_left_conv
    relatedTripleCoordinateAntipode_right_conv

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
