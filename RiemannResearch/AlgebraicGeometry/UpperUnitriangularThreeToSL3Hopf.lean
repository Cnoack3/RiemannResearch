/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SpecialLinearThreeCoordinateHopf
import RiemannResearch.AlgebraicGeometry.UpperUnitriangularThreeCoordinatePoints

/-!
# The upper-unitriangular subgroup of split `SL₃` on coordinate Hopf algebras

This file represents the standard inclusion `U₃ → SL₃`.  Contravariantly it
constructs the pullback

`O(SL₃) → O(U₃) = ℤ[x₁₂,x₂₃,x₁₃]`

from the universal upper-unitriangular matrix.  It proves specialization over
every commutative ring, compatibility with all Hopf structure maps, and the
resulting affine group-scheme morphism.
-/

open CategoryTheory
open scoped TensorProduct

namespace RiemannResearch
namespace AlgebraicGeometry
namespace UpperUnitriangularThree

noncomputable section

private abbrev A := SpecialLinearThree.Coordinate
private abbrev P := Coordinate
private abbrev T := A ⊗[ℤ] A
private abbrev Q := P ⊗[ℤ] P

local instance coordinateAddCommMonoid : AddCommMonoid A :=
  (inferInstance : Semiring A).toAddCommMonoid

local instance coordinateIntModule : Module ℤ A :=
  @Algebra.toModule ℤ A _ _ (inferInstance : Algebra ℤ A)

noncomputable local instance sourceTensorRing : Ring T :=
  SpecialLinearThree.tensorProductRing

noncomputable local instance sourceTensorCommRing : CommRing T :=
  SpecialLinearThree.tensorProductCommRing

local instance sourceTensorAlgebra : Algebra ℤ T :=
  @Algebra.TensorProduct.instAlgebra ℤ A A
    (inferInstance : CommSemiring ℤ)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)

noncomputable local instance sl3Hopf : HopfAlgebra ℤ A :=
  SpecialLinearThree.coordinateHopfAlgebra

noncomputable local instance u3ToSL3Hopf : HopfAlgebra ℤ P :=
  hopfAlgebra

/-- The tautological upper-unitriangular point over its coordinate algebra. -/
def universalPoint : Point P := ⟨x12, x23, x13⟩

/-- The universal upper-unitriangular matrix, viewed as an `SL₃`-point. -/
def universalSL3Point : Matrix.SpecialLinearGroup (Fin 3) P :=
  Point.toSL3 universalPoint

/-- Pullback of regular functions along the standard inclusion `U₃ → SL₃`. -/
def toSL3AlgHom : A →ₐ[ℤ] P :=
  SpecialLinearThree.coordinateAlgHomOfRingHom
    (SpecialLinearThree.coordinateEvaluation universalSL3Point)

@[simp] theorem toSL3AlgHom_quotient_X (i j : Fin 3) :
    toSL3AlgHom (SpecialLinearThree.quotient (MvPolynomial.X (i, j))) =
      (!![1, x12, x13; 0, 1, x23; 0, 0, 1] :
        Matrix (Fin 3) (Fin 3) P) i j := by
  change SpecialLinearThree.coordinateEvaluation universalSL3Point
      (SpecialLinearThree.quotient (MvPolynomial.X (i, j))) = _
  rw [SpecialLinearThree.coordinateEvaluation_quotient_X]
  rw [universalSL3Point, Point.toSL3_matrix]
  simp [universalPoint]

/-- The pullback sends the universal `SL₃` point to the universal
upper-unitriangular matrix. -/
theorem toSL3AlgHom_universal :
    Matrix.SpecialLinearGroup.map toSL3AlgHom.toRingHom
      SpecialLinearThree.universalPoint = universalSL3Point := by
  change Matrix.SpecialLinearGroup.map
    (SpecialLinearThree.coordinateEvaluation universalSL3Point)
      SpecialLinearThree.universalPoint = universalSL3Point
  exact SpecialLinearThree.coordinateEvaluation_universal _

namespace Point

/-- The standard embedding in `SL₃` commutes with base change. -/
theorem toSL3_map
    {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Point R) :
    Matrix.SpecialLinearGroup.map f (toSL3 p) =
      toSL3 (map f p) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change f ((((toSL3 p : Matrix.SpecialLinearGroup (Fin 3) R) :
      Matrix (Fin 3) (Fin 3) R) i j)) =
    (((toSL3 (map f p) : Matrix.SpecialLinearGroup (Fin 3) S) :
      Matrix (Fin 3) (Fin 3) S) i j)
  rw [toSL3_matrix, toSL3_matrix]
  fin_cases i <;> fin_cases j <;> simp [map]

end Point

/-- Every specialization of the coordinate pullback is the pointwise
upper-unitriangular embedding. -/
theorem toSL3AlgHom_specialization
    {S : Type} [CommRing S] (f : P →+* S) :
    SpecialLinearThree.coordinateRingHomEquiv S
      (f.comp toSL3AlgHom.toRingHom) =
      Point.toSL3 (coordinateRingHomEquiv S f) := by
  change Matrix.SpecialLinearGroup.map
      (f.comp toSL3AlgHom.toRingHom)
      SpecialLinearThree.universalPoint = _
  rw [SpecialLinearThree.specialLinearMap_comp_apply]
  rw [toSL3AlgHom_universal]
  change Matrix.SpecialLinearGroup.map f (Point.toSL3 universalPoint) = _
  rw [Point.toSL3_map]
  rfl

private def targetIncludeLeft : P →ₐ[ℤ] Q :=
  Algebra.TensorProduct.includeLeft

private def targetIncludeRight : P →ₐ[ℤ] Q :=
  Algebra.TensorProduct.includeRight

private theorem tensorMap_includeLeft :
    (Algebra.TensorProduct.map toSL3AlgHom toSL3AlgHom).toRingHom.comp
        SpecialLinearThree.tensorIncludeLeft =
      targetIncludeLeft.toRingHom.comp toSL3AlgHom.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [SpecialLinearThree.tensorIncludeLeft, targetIncludeLeft]

private theorem tensorMap_includeRight :
    (Algebra.TensorProduct.map toSL3AlgHom toSL3AlgHom).toRingHom.comp
        SpecialLinearThree.tensorIncludeRight =
      targetIncludeRight.toRingHom.comp toSL3AlgHom.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  change (Algebra.TensorProduct.map toSL3AlgHom toSL3AlgHom)
      ((1 : A) ⊗ₜ[ℤ] x) = (1 : P) ⊗ₜ[ℤ] toSL3AlgHom x
  rw [Algebra.TensorProduct.map_tmul]
  simp

private theorem tensorMap_universalPointLeft :
    Matrix.SpecialLinearGroup.map
      (Algebra.TensorProduct.map toSL3AlgHom toSL3AlgHom).toRingHom
        SpecialLinearThree.universalPointLeft =
      Matrix.SpecialLinearGroup.map targetIncludeLeft.toRingHom
        universalSL3Point := by
  rw [SpecialLinearThree.universalPointLeft]
  rw [← SpecialLinearThree.specialLinearMap_comp_apply]
  rw [tensorMap_includeLeft]
  rw [SpecialLinearThree.specialLinearMap_comp_apply]
  rw [toSL3AlgHom_universal]

private theorem tensorMap_universalPointRight :
    Matrix.SpecialLinearGroup.map
      (Algebra.TensorProduct.map toSL3AlgHom toSL3AlgHom).toRingHom
        SpecialLinearThree.universalPointRight =
      Matrix.SpecialLinearGroup.map targetIncludeRight.toRingHom
        universalSL3Point := by
  rw [SpecialLinearThree.universalPointRight]
  rw [← SpecialLinearThree.specialLinearMap_comp_apply]
  rw [tensorMap_includeRight]
  rw [SpecialLinearThree.specialLinearMap_comp_apply]
  rw [toSL3AlgHom_universal]

private theorem universalPoint_comul :
    Point.map targetIncludeLeft.toRingHom universalPoint *
      Point.map targetIncludeRight.toRingHom universalPoint =
    Point.map comul.toRingHom universalPoint := by
  ext
  · change targetIncludeLeft x12 + targetIncludeRight x12 = comul x12
    rw [comul_x12]
    simp [targetIncludeLeft, targetIncludeRight,
      Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]
  · change targetIncludeLeft x23 + targetIncludeRight x23 = comul x23
    rw [comul_x23]
    simp [targetIncludeLeft, targetIncludeRight,
      Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]
  · change targetIncludeLeft x13 + targetIncludeRight x13 +
        targetIncludeLeft x12 * targetIncludeRight x23 = comul x13
    rw [comul_x13]
    simp [targetIncludeLeft, targetIncludeRight,
      Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]

private theorem universalSL3Point_comul :
    Matrix.SpecialLinearGroup.map targetIncludeLeft.toRingHom universalSL3Point *
      Matrix.SpecialLinearGroup.map targetIncludeRight.toRingHom
        universalSL3Point =
    Matrix.SpecialLinearGroup.map comul.toRingHom universalSL3Point := by
  rw [universalSL3Point, Point.toSL3_map, Point.toSL3_map, Point.toSL3_map]
  calc
    Point.toSL3 (Point.map targetIncludeLeft.toRingHom universalPoint) *
        Point.toSL3 (Point.map targetIncludeRight.toRingHom universalPoint) =
      Point.toSL3
        (Point.map targetIncludeLeft.toRingHom universalPoint *
          Point.map targetIncludeRight.toRingHom universalPoint) :=
      ((Point.toSL3Hom (S := Q)).map_mul _ _).symm
    _ = Point.toSL3 (Point.map comul.toRingHom universalPoint) :=
      congrArg Point.toSL3 universalPoint_comul

/-- The coordinate pullback preserves comultiplication. -/
theorem toSL3AlgHom_comul :
    (Algebra.TensorProduct.map toSL3AlgHom toSL3AlgHom).comp
        SpecialLinearThree.coordinateComul =
      comul.comp toSL3AlgHom := by
  apply SpecialLinearThree.coordinateAlgHom_ext
  rw [SpecialLinearThree.coordinateComul_baseChange]
  rw [tensorMap_universalPointLeft, tensorMap_universalPointRight]
  change _ = Matrix.SpecialLinearGroup.map
    (comul.toRingHom.comp toSL3AlgHom.toRingHom)
      SpecialLinearThree.universalPoint
  rw [SpecialLinearThree.specialLinearMap_comp_apply]
  rw [toSL3AlgHom_universal]
  exact universalSL3Point_comul

private theorem universalPoint_counit :
    Point.map counit.toRingHom universalPoint = (1 : Point ℤ) := by
  ext <;> simp [universalPoint]

private theorem universalSL3Point_counit :
    Matrix.SpecialLinearGroup.map counit.toRingHom universalSL3Point =
      (1 : Matrix.SpecialLinearGroup (Fin 3) ℤ) := by
  rw [universalSL3Point, Point.toSL3_map]
  rw [universalPoint_counit]
  exact (Point.toSL3Hom (S := ℤ)).map_one

/-- The coordinate pullback preserves the counit. -/
theorem toSL3AlgHom_counit :
    counit.comp toSL3AlgHom =
      SpecialLinearThree.coordinateCounit := by
  apply SpecialLinearThree.coordinateAlgHom_ext
  change Matrix.SpecialLinearGroup.map
      (counit.toRingHom.comp toSL3AlgHom.toRingHom)
        SpecialLinearThree.universalPoint =
    Matrix.SpecialLinearGroup.map
      SpecialLinearThree.coordinateCounit.toRingHom
        SpecialLinearThree.universalPoint
  rw [SpecialLinearThree.specialLinearMap_comp_apply]
  rw [toSL3AlgHom_universal]
  rw [SpecialLinearThree.coordinateCounit_universal]
  exact universalSL3Point_counit

private theorem universalPoint_antipode :
    Point.map antipode.toRingHom universalPoint = universalPoint⁻¹ := by
  ext <;> simp [universalPoint]

private theorem universalSL3Point_antipode :
    Matrix.SpecialLinearGroup.map antipode.toRingHom universalSL3Point =
      universalSL3Point⁻¹ := by
  rw [universalSL3Point, Point.toSL3_map]
  rw [universalPoint_antipode]
  exact (Point.toSL3Hom (S := P)).map_inv universalPoint

/-- The coordinate pullback preserves the antipode. -/
theorem toSL3AlgHom_antipode :
    antipode.comp toSL3AlgHom =
      toSL3AlgHom.comp SpecialLinearThree.coordinateAntipode := by
  apply SpecialLinearThree.coordinateAlgHom_ext
  change Matrix.SpecialLinearGroup.map
      (antipode.toRingHom.comp toSL3AlgHom.toRingHom)
        SpecialLinearThree.universalPoint =
    Matrix.SpecialLinearGroup.map
      (toSL3AlgHom.toRingHom.comp
        SpecialLinearThree.coordinateAntipode.toRingHom)
        SpecialLinearThree.universalPoint
  rw [SpecialLinearThree.specialLinearMap_comp_apply]
  rw [toSL3AlgHom_universal]
  rw [SpecialLinearThree.specialLinearMap_comp_apply]
  rw [SpecialLinearThree.coordinateAntipode_universal]
  rw [map_inv]
  rw [toSL3AlgHom_universal]
  exact universalSL3Point_antipode

private theorem toSL3AlgHom_counit_linear :
    CoalgebraStruct.counit ∘ₗ toSL3AlgHom.toLinearMap =
      CoalgebraStruct.counit := by
  change counit.toLinearMap ∘ₗ toSL3AlgHom.toLinearMap =
    SpecialLinearThree.coordinateCounit.toLinearMap
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun toSL3AlgHom_counit x

private theorem toSL3AlgHom_comul_linear :
    TensorProduct.map toSL3AlgHom.toLinearMap toSL3AlgHom.toLinearMap ∘ₗ
        CoalgebraStruct.comul =
      CoalgebraStruct.comul ∘ₗ toSL3AlgHom.toLinearMap := by
  change TensorProduct.map toSL3AlgHom.toLinearMap toSL3AlgHom.toLinearMap ∘ₗ
      SpecialLinearThree.coordinateComul.toLinearMap =
    comul.toLinearMap ∘ₗ toSL3AlgHom.toLinearMap
  apply LinearMap.ext
  intro x
  change (Algebra.TensorProduct.map toSL3AlgHom toSL3AlgHom)
      (SpecialLinearThree.coordinateComul x) =
    comul (toSL3AlgHom x)
  exact DFunLike.congr_fun toSL3AlgHom_comul x

/-- The bialgebra morphism representing the standard inclusion `U₃ → SL₃`.
Together with `toSL3AlgHom_antipode`, this is the full coordinate-Hopf
morphism. -/
noncomputable def toSL3BialgHom : A →ₐc[ℤ] P :=
  BialgHom.mk
    (CoalgHom.mk toSL3AlgHom.toLinearMap
      toSL3AlgHom_counit_linear
      toSL3AlgHom_comul_linear)
    toSL3AlgHom.map_one
    toSL3AlgHom.map_mul

theorem toSL3BialgHom_toAlgHom :
    toSL3BialgHom.toAlgHom = toSL3AlgHom := by
  apply AlgHom.ext
  intro x
  rfl

/-- Specializing the bundled bialgebra morphism recovers the standard
upper-unitriangular embedding on points. -/
theorem toSL3BialgHom_specialization
    {S : Type} [CommRing S] (f : P →+* S) :
    SpecialLinearThree.coordinateRingHomEquiv S
      (f.comp toSL3BialgHom.toAlgHom.toRingHom) =
      Point.toSL3 (coordinateRingHomEquiv S f) := by
  rw [toSL3BialgHom_toAlgHom]
  exact toSL3AlgHom_specialization f

/-- The affine group-scheme morphism `U₃ → SL₃` induced by the coordinate
bialgebra morphism. -/
noncomputable def toSL3GroupSchemeHom :
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj
      (Opposite.op (CommHopfAlgCat.of ℤ P))) ⟶
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj
      (Opposite.op (CommHopfAlgCat.of ℤ A))) :=
  (_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
    (CommHopfAlgCat.ofHom toSL3BialgHom).op

end
end UpperUnitriangularThree
end AlgebraicGeometry
end RiemannResearch
