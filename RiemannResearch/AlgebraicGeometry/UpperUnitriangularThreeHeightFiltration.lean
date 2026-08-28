/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AdditiveGroupPointConvolution
import RiemannResearch.AlgebraicGeometry.AdditiveVectorGroupPoints
import RiemannResearch.AlgebraicGeometry.UpperUnitriangularThreeCoordinatePoints

/-!
# The central height filtration of the split upper-unitriangular group

This file lifts the pointwise height filtration of `U₃` to coordinate Hopf
algebras and affine group schemes.  It constructs the sequence

`Gₐ → U₃ → Gₐ²`

where the first map is the highest-root center and the second map remembers
the two simple-root coordinates.  On points over every commutative ring the
first map is injective, the second is surjective, and the image of the first
is exactly the kernel of the second.

Contravariantly, the coordinate maps preserve comultiplication, counit, and
antipode, and therefore induce morphisms through `hopfSpec`.
-/

open CategoryTheory
open scoped TensorProduct

namespace RiemannResearch
namespace AlgebraicGeometry
namespace UpperUnitriangularThree

noncomputable section

/-- Coordinate algebra of the central `Gₐ`. -/
abbrev CenterCoordinate := AdditiveGroup.Coordinate ℤ

/-- Coordinate algebra of the height-one quotient `Gₐ²`. -/
abbrev HeightOneCoordinate :=
  AdditiveVectorGroup.Coordinate ℤ (Fin 2)

noncomputable local instance u3Hopf :
    HopfAlgebra ℤ Coordinate := hopfAlgebra

noncomputable local instance centerHopf :
    HopfAlgebra ℤ CenterCoordinate :=
  AdditiveGroup.hopfAlgebra ℤ

noncomputable local instance heightOneHopf :
    HopfAlgebra ℤ HeightOneCoordinate :=
  AdditiveVectorGroup.hopfAlgebra ℤ (Fin 2)

namespace Point

variable {S : Type} [CommRing S]

/-- Projection to the two simple-root coordinates, as a vector group. -/
def vectorProjection :
    Point S →* Multiplicative (Fin 2 → S) where
  toFun x := Multiplicative.ofAdd ![x.root12, x.root23]
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl

@[simp] theorem vectorProjection_apply (x : Point S) :
    (vectorProjection x).toAdd = ![x.root12, x.root23] := rfl

@[simp] theorem vectorProjection_center (c : S) :
    vectorProjection (center c) = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> rfl

@[simp] theorem mem_ker_vectorProjection_iff (x : Point S) :
    x ∈ MonoidHom.ker (vectorProjection (S := S)) ↔
      x.root12 = 0 ∧ x.root23 = 0 := by
  constructor
  · intro hx
    change Multiplicative.ofAdd ![x.root12, x.root23] = 1 at hx
    have h := congrArg Multiplicative.toAdd hx
    constructor
    · exact congrFun h 0
    · exact congrFun h 1
  · rintro ⟨h12, h23⟩
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp [h12, h23]

/-- Projection to the height-one quotient is surjective on points over every
commutative ring. -/
theorem vectorProjection_surjective :
    Function.Surjective (vectorProjection (S := S)) := by
  intro v
  refine ⟨⟨v.toAdd 0, v.toAdd 1, 0⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> rfl

/-- The central highest-root subgroup is exactly the kernel of the
height-one projection. -/
theorem ker_vectorProjection_eq_range_centerHom :
    MonoidHom.ker (vectorProjection (S := S)) =
      MonoidHom.range (centerHom (S := S)) := by
  ext x
  constructor
  · intro hx
    rw [mem_ker_vectorProjection_iff] at hx
    rcases hx with ⟨h12, h23⟩
    refine ⟨Multiplicative.ofAdd x.root13, ?_⟩
    ext <;> simp [centerHom, center, h12, h23]
  · rintro ⟨c, rfl⟩
    exact vectorProjection_center c.toAdd

/-- Pointwise exactness of `1 → Gₐ → U₃ → Gₐ² → 1`. -/
theorem heightFiltration_exact :
    Function.Injective (centerHom (S := S)) ∧
      Function.Surjective (vectorProjection (S := S)) ∧
      MonoidHom.ker (vectorProjection (S := S)) =
        MonoidHom.range (centerHom (S := S)) := by
  exact ⟨centerHom_injective, vectorProjection_surjective,
    ker_vectorProjection_eq_range_centerHom⟩

/-- First-isomorphism identification of the height-one quotient with the
two-dimensional additive vector group. -/
noncomputable def vectorQuotientEquiv :
    Point S ⧸ MonoidHom.ker (vectorProjection (S := S)) ≃*
      Multiplicative (Fin 2 → S) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (vectorProjection (S := S)) vectorProjection_surjective

end Point

/-- Pullback on coordinate rings for the central inclusion `Gₐ → U₃`. -/
def centerAlgHom : Coordinate →ₐ[ℤ] CenterCoordinate :=
  MvPolynomial.aeval
    ![(0 : CenterCoordinate), (0 : CenterCoordinate), Polynomial.X]

@[simp] theorem centerAlgHom_x12 :
    centerAlgHom x12 = 0 := by
  simp [centerAlgHom, x12]

@[simp] theorem centerAlgHom_x23 :
    centerAlgHom x23 = 0 := by
  simp [centerAlgHom, x23]

@[simp] theorem centerAlgHom_x13 :
    centerAlgHom x13 = Polynomial.X := by
  simp [centerAlgHom, x13]

/-- The central coordinate pullback preserves comultiplication. -/
theorem centerAlgHom_comul :
    (Algebra.TensorProduct.map centerAlgHom centerAlgHom).comp comul =
      (AdditiveGroup.comul ℤ).comp centerAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [AlgHom.comp_apply, centerAlgHom]
  · simp [AlgHom.comp_apply, centerAlgHom]
  · simp [AlgHom.comp_apply, centerAlgHom, AdditiveGroup.comul,
      Algebra.TensorProduct.includeLeft,
      Algebra.TensorProduct.includeRight]

/-- The central coordinate pullback preserves the counit. -/
theorem centerAlgHom_counit :
    (AdditiveGroup.counit ℤ).comp centerAlgHom = counit := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [AlgHom.comp_apply, centerAlgHom, AdditiveGroup.counit]

/-- The central coordinate pullback preserves the antipode. -/
theorem centerAlgHom_antipode :
    (AdditiveGroup.antipode ℤ).comp centerAlgHom =
      centerAlgHom.comp antipode := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [AlgHom.comp_apply, centerAlgHom, AdditiveGroup.antipode]

/-- Pullback on coordinate rings for the quotient projection `U₃ → Gₐ²`. -/
def projectionAlgHom : HeightOneCoordinate →ₐ[ℤ] Coordinate :=
  MvPolynomial.aeval ![x12, x23]

@[simp] theorem projectionAlgHom_X_zero :
    projectionAlgHom (MvPolynomial.X (0 : Fin 2)) = x12 := by
  simp [projectionAlgHom]

@[simp] theorem projectionAlgHom_X_one :
    projectionAlgHom (MvPolynomial.X (1 : Fin 2)) = x23 := by
  simp [projectionAlgHom]

/-- The quotient coordinate pullback preserves comultiplication. -/
theorem projectionAlgHom_comul :
    (Algebra.TensorProduct.map projectionAlgHom projectionAlgHom).comp
        (AdditiveVectorGroup.comul ℤ (Fin 2)) =
      comul.comp projectionAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, AlgHom.comp_apply,
    AdditiveVectorGroup.comul_X]
  fin_cases i <;>
    simp [projectionAlgHom, Algebra.TensorProduct.map_tmul]

/-- The quotient coordinate pullback preserves the counit. -/
theorem projectionAlgHom_counit :
    counit.comp projectionAlgHom =
      AdditiveVectorGroup.counit ℤ (Fin 2) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [AlgHom.comp_apply, projectionAlgHom,
      AdditiveVectorGroup.counit]

/-- The quotient coordinate pullback preserves the antipode. -/
theorem projectionAlgHom_antipode :
    antipode.comp projectionAlgHom =
      projectionAlgHom.comp
        (AdditiveVectorGroup.antipode ℤ (Fin 2)) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [AlgHom.comp_apply, projectionAlgHom,
      AdditiveVectorGroup.antipode]

/-- The zero point of the height-one vector group, with values in the central
coordinate algebra. -/
def zeroVectorAlgHom : HeightOneCoordinate →ₐ[ℤ] CenterCoordinate :=
  MvPolynomial.aeval (fun _ : Fin 2 => (0 : CenterCoordinate))

/-- The composite `Gₐ → U₃ → Gₐ²` is the zero morphism on coordinate
algebras. -/
theorem center_projection_zero :
    centerAlgHom.comp projectionAlgHom = zeroVectorAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [centerAlgHom, projectionAlgHom, zeroVectorAlgHom]

private theorem centerAlgHom_counit_linear :
    CoalgebraStruct.counit ∘ₗ centerAlgHom.toLinearMap =
      CoalgebraStruct.counit := by
  change (AdditiveGroup.counit ℤ).toLinearMap ∘ₗ
      centerAlgHom.toLinearMap = counit.toLinearMap
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun centerAlgHom_counit x

private theorem centerAlgHom_comul_linear :
    TensorProduct.map centerAlgHom.toLinearMap centerAlgHom.toLinearMap ∘ₗ
        CoalgebraStruct.comul =
      CoalgebraStruct.comul ∘ₗ centerAlgHom.toLinearMap := by
  change TensorProduct.map centerAlgHom.toLinearMap centerAlgHom.toLinearMap ∘ₗ
      comul.toLinearMap =
    (AdditiveGroup.comul ℤ).toLinearMap ∘ₗ centerAlgHom.toLinearMap
  apply LinearMap.ext
  intro x
  change (Algebra.TensorProduct.map centerAlgHom centerAlgHom) (comul x) =
    AdditiveGroup.comul ℤ (centerAlgHom x)
  exact DFunLike.congr_fun centerAlgHom_comul x

/-- The bialgebra morphism representing the central inclusion `Gₐ → U₃`. -/
noncomputable def centerBialgHom :
    Coordinate →ₐc[ℤ] CenterCoordinate :=
  BialgHom.mk
    (CoalgHom.mk centerAlgHom.toLinearMap
      centerAlgHom_counit_linear
      centerAlgHom_comul_linear)
    centerAlgHom.map_one
    centerAlgHom.map_mul

theorem centerBialgHom_toAlgHom :
    centerBialgHom.toAlgHom = centerAlgHom := by
  apply AlgHom.ext
  intro x
  rfl

private theorem projectionAlgHom_counit_linear :
    CoalgebraStruct.counit ∘ₗ projectionAlgHom.toLinearMap =
      CoalgebraStruct.counit := by
  change counit.toLinearMap ∘ₗ projectionAlgHom.toLinearMap =
    (AdditiveVectorGroup.counit ℤ (Fin 2)).toLinearMap
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun projectionAlgHom_counit x

private theorem projectionAlgHom_comul_linear :
    TensorProduct.map projectionAlgHom.toLinearMap
        projectionAlgHom.toLinearMap ∘ₗ CoalgebraStruct.comul =
      CoalgebraStruct.comul ∘ₗ projectionAlgHom.toLinearMap := by
  change TensorProduct.map projectionAlgHom.toLinearMap
        projectionAlgHom.toLinearMap ∘ₗ
      (AdditiveVectorGroup.comul ℤ (Fin 2)).toLinearMap =
    comul.toLinearMap ∘ₗ projectionAlgHom.toLinearMap
  apply LinearMap.ext
  intro x
  change (Algebra.TensorProduct.map projectionAlgHom projectionAlgHom)
      (AdditiveVectorGroup.comul ℤ (Fin 2) x) =
    comul (projectionAlgHom x)
  exact DFunLike.congr_fun projectionAlgHom_comul x

/-- The bialgebra morphism representing the quotient projection
`U₃ → Gₐ²`. -/
noncomputable def projectionBialgHom :
    HeightOneCoordinate →ₐc[ℤ] Coordinate :=
  BialgHom.mk
    (CoalgHom.mk projectionAlgHom.toLinearMap
      projectionAlgHom_counit_linear
      projectionAlgHom_comul_linear)
    projectionAlgHom.map_one
    projectionAlgHom.map_mul

theorem projectionBialgHom_toAlgHom :
    projectionBialgHom.toAlgHom = projectionAlgHom := by
  apply AlgHom.ext
  intro x
  rfl

/-- Specialization of the central coordinate map is the pointwise
highest-root inclusion. -/
theorem centerAlgHom_specialization
    {S : Type} [CommRing S] (f : CenterCoordinate →+* S) :
    coordinateRingHomEquiv S (f.comp centerAlgHom.toRingHom) =
      Point.center (f Polynomial.X) := by
  ext <;> simp [centerAlgHom, Point.center]

/-- Specialization of the quotient coordinate map is projection to the two
simple-root coordinates. -/
theorem projectionAlgHom_specialization
    {S : Type} [CommRing S] (f : Coordinate →+* S) :
    AdditiveVectorGroup.coordinateAlgHomEquiv ℤ (Fin 2) S
        ((f.comp projectionAlgHom.toRingHom).toIntAlgHom) =
      (Point.vectorProjection (coordinateRingHomEquiv S f)).toAdd := by
  funext i
  fin_cases i
  · change f (projectionAlgHom (MvPolynomial.X (0 : Fin 2))) = f x12
    rw [projectionAlgHom_X_zero]
  · change f (projectionAlgHom (MvPolynomial.X (1 : Fin 2))) = f x23
    rw [projectionAlgHom_X_one]

/-- The affine group-scheme morphism for the central inclusion
`Gₐ → U₃`. -/
noncomputable def centerGroupSchemeHom :
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj
      (Opposite.op (CommHopfAlgCat.of ℤ CenterCoordinate))) ⟶
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj
      (Opposite.op (CommHopfAlgCat.of ℤ Coordinate))) :=
  (_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
    (CommHopfAlgCat.ofHom centerBialgHom).op

/-- The affine group-scheme morphism for the quotient projection
`U₃ → Gₐ²`. -/
noncomputable def projectionGroupSchemeHom :
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj
      (Opposite.op (CommHopfAlgCat.of ℤ Coordinate))) ⟶
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj
      (Opposite.op (CommHopfAlgCat.of ℤ HeightOneCoordinate))) :=
  (_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
    (CommHopfAlgCat.ofHom projectionBialgHom).op

/-- The scheme maps induce an exact central height filtration on points over
every commutative ring. -/
theorem heightFiltration_exact_on_points
    (S : Type) [CommRing S] :
    Function.Injective (Point.centerHom (S := S)) ∧
      Function.Surjective (Point.vectorProjection (S := S)) ∧
      MonoidHom.ker (Point.vectorProjection (S := S)) =
        MonoidHom.range (Point.centerHom (S := S)) :=
  Point.heightFiltration_exact

end
end UpperUnitriangularThree
end AlgebraicGeometry
end RiemannResearch
