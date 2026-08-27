/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AdditiveGroupScheme
import RiemannResearch.AlgebraicGeometry.ChevalleyA2Relations
import RiemannResearch.AlgebraicGeometry.SpecialLinearThreeCoordinateHopf

/-!
# Integral type-A2 root subgroup Hopf morphisms

This file constructs the coordinate-Hopf morphisms `O(SL₃) → ℤ[X]`
representing every elementary transvection root subgroup `Gₐ → SL₃`.
The construction preserves counit and comultiplication, specializes to the
usual transvection matrix over every commutative ring, and passes through
Mathlib's `hopfSpec` to produce affine group-scheme morphisms.

The final specializations name the three positive roots of the standard
type-A2 subsystem: `x₁₂`, `x₂₃`, and `x₁₃`.  These are the represented root
maps needed to lift the pointwise Chevalley commutator formula to the affine
group-scheme level.  This file does not yet construct the split E8 group.
-/

open CategoryTheory
open scoped TensorProduct

namespace RiemannResearch
namespace AlgebraicGeometry
namespace SpecialLinearThreeRootSubgroups

noncomputable section

private abbrev A := SpecialLinearThree.Coordinate
private abbrev P := AdditiveGroup.Coordinate ℤ
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

noncomputable local instance additiveHopf : HopfAlgebra ℤ P :=
  AdditiveGroup.hopfAlgebra ℤ

/-- The universal elementary transvection with polynomial parameter `X`. -/
def rootPoint (i j : Fin 3) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup (Fin 3) P :=
  ChevalleyRankOne.transvectionRoot P i j hij
    (Multiplicative.ofAdd (Polynomial.X : P))

/-- Pullback of regular functions along the universal transvection. -/
def rootAlgHom (i j : Fin 3) (hij : i ≠ j) : A →ₐ[ℤ] P :=
  SpecialLinearThree.coordinateAlgHomOfRingHom
    (SpecialLinearThree.coordinateEvaluation (rootPoint i j hij))

@[simp] theorem rootAlgHom_quotient_X
    (i j : Fin 3) (hij : i ≠ j) (r s : Fin 3) :
    rootAlgHom i j hij
        (SpecialLinearThree.quotient (MvPolynomial.X (r, s))) =
      Matrix.transvection i j (Polynomial.X : P) r s := by
  change SpecialLinearThree.coordinateEvaluation (rootPoint i j hij)
      (SpecialLinearThree.quotient (MvPolynomial.X (r, s))) = _
  rw [SpecialLinearThree.coordinateEvaluation_quotient_X]
  rfl

theorem rootAlgHom_universal (i j : Fin 3) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.map (rootAlgHom i j hij).toRingHom
      SpecialLinearThree.universalPoint = rootPoint i j hij := by
  change Matrix.SpecialLinearGroup.map
    (SpecialLinearThree.coordinateEvaluation (rootPoint i j hij))
      SpecialLinearThree.universalPoint = rootPoint i j hij
  exact SpecialLinearThree.coordinateEvaluation_universal _

theorem rootPoint_natural
    (i j : Fin 3) (hij : i ≠ j)
    {R : Type} [CommRing R] (f : P →+* R) :
    Matrix.SpecialLinearGroup.map f (rootPoint i j hij) =
      ChevalleyRankOne.transvectionRoot R i j hij
        (Multiplicative.ofAdd (f Polynomial.X)) := by
  exact ChevalleyRankOne.transvectionRoot_natural P f i j hij
    (Multiplicative.ofAdd (Polynomial.X : P))

private def additiveIncludeLeft : P →ₐ[ℤ] Q :=
  Algebra.TensorProduct.includeLeft

private def additiveIncludeRight : P →ₐ[ℤ] Q :=
  Algebra.TensorProduct.includeRight

private theorem tensorMap_includeLeft
    (i j : Fin 3) (hij : i ≠ j) :
    (Algebra.TensorProduct.map (rootAlgHom i j hij)
        (rootAlgHom i j hij)).toRingHom.comp
        SpecialLinearThree.tensorIncludeLeft =
      additiveIncludeLeft.toRingHom.comp
        (rootAlgHom i j hij).toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [SpecialLinearThree.tensorIncludeLeft, additiveIncludeLeft]

private theorem tensorMap_includeRight
    (i j : Fin 3) (hij : i ≠ j) :
    (Algebra.TensorProduct.map (rootAlgHom i j hij)
        (rootAlgHom i j hij)).toRingHom.comp
        SpecialLinearThree.tensorIncludeRight =
      additiveIncludeRight.toRingHom.comp
        (rootAlgHom i j hij).toRingHom := by
  apply DFunLike.ext _ _
  intro x
  change (Algebra.TensorProduct.map (rootAlgHom i j hij)
      (rootAlgHom i j hij)) ((1 : A) ⊗ₜ[ℤ] x) =
    (1 : P) ⊗ₜ[ℤ] (rootAlgHom i j hij) x
  rw [Algebra.TensorProduct.map_tmul]
  simp

private theorem tensorMap_universalPointLeft
    (i j : Fin 3) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.map
      (Algebra.TensorProduct.map (rootAlgHom i j hij)
        (rootAlgHom i j hij)).toRingHom
        SpecialLinearThree.universalPointLeft =
      Matrix.SpecialLinearGroup.map additiveIncludeLeft.toRingHom
        (rootPoint i j hij) := by
  rw [SpecialLinearThree.universalPointLeft]
  rw [← SpecialLinearThree.specialLinearMap_comp_apply]
  rw [tensorMap_includeLeft]
  rw [SpecialLinearThree.specialLinearMap_comp_apply]
  rw [rootAlgHom_universal]

private theorem tensorMap_universalPointRight
    (i j : Fin 3) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.map
      (Algebra.TensorProduct.map (rootAlgHom i j hij)
        (rootAlgHom i j hij)).toRingHom
        SpecialLinearThree.universalPointRight =
      Matrix.SpecialLinearGroup.map additiveIncludeRight.toRingHom
        (rootPoint i j hij) := by
  rw [SpecialLinearThree.universalPointRight]
  rw [← SpecialLinearThree.specialLinearMap_comp_apply]
  rw [tensorMap_includeRight]
  rw [SpecialLinearThree.specialLinearMap_comp_apply]
  rw [rootAlgHom_universal]

private theorem rootPoint_comul
    (i j : Fin 3) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.map additiveIncludeLeft.toRingHom
        (rootPoint i j hij) *
      Matrix.SpecialLinearGroup.map additiveIncludeRight.toRingHom
        (rootPoint i j hij) =
      Matrix.SpecialLinearGroup.map (AdditiveGroup.comul ℤ).toRingHom
        (rootPoint i j hij) := by
  rw [rootPoint_natural, rootPoint_natural, rootPoint_natural]
  rw [← map_mul]
  congr 1
  change additiveIncludeLeft Polynomial.X +
      additiveIncludeRight Polynomial.X =
    (AdditiveGroup.comul ℤ) Polynomial.X
  simp [additiveIncludeLeft, additiveIncludeRight, AdditiveGroup.comul,
    Algebra.TensorProduct.includeLeft,
    Algebra.TensorProduct.includeRight]

/-- The root pullback preserves comultiplication. -/
theorem rootAlgHom_comul
    (i j : Fin 3) (hij : i ≠ j) :
    (Algebra.TensorProduct.map (rootAlgHom i j hij)
        (rootAlgHom i j hij)).comp
        SpecialLinearThree.coordinateComul =
      (AdditiveGroup.comul ℤ).comp (rootAlgHom i j hij) := by
  apply SpecialLinearThree.coordinateAlgHom_ext
  rw [SpecialLinearThree.coordinateComul_baseChange]
  rw [tensorMap_universalPointLeft, tensorMap_universalPointRight]
  change _ = Matrix.SpecialLinearGroup.map
    ((AdditiveGroup.comul ℤ).toRingHom.comp
      (rootAlgHom i j hij).toRingHom)
      SpecialLinearThree.universalPoint
  rw [SpecialLinearThree.specialLinearMap_comp_apply]
  rw [rootAlgHom_universal]
  exact rootPoint_comul i j hij

/-- The root pullback preserves the counit. -/
theorem rootAlgHom_counit
    (i j : Fin 3) (hij : i ≠ j) :
    (AdditiveGroup.counit ℤ).comp (rootAlgHom i j hij) =
      SpecialLinearThree.coordinateCounit := by
  apply SpecialLinearThree.coordinateAlgHom_ext
  change Matrix.SpecialLinearGroup.map
      ((AdditiveGroup.counit ℤ).toRingHom.comp
        (rootAlgHom i j hij).toRingHom)
        SpecialLinearThree.universalPoint =
    Matrix.SpecialLinearGroup.map
      SpecialLinearThree.coordinateCounit.toRingHom
        SpecialLinearThree.universalPoint
  rw [SpecialLinearThree.specialLinearMap_comp_apply]
  rw [rootAlgHom_universal]
  rw [SpecialLinearThree.coordinateCounit_universal]
  rw [rootPoint_natural]
  change ChevalleyRankOne.transvectionRoot ℤ i j hij
      (Multiplicative.ofAdd
        ((AdditiveGroup.counit ℤ) Polynomial.X)) = 1
  rw [show (AdditiveGroup.counit ℤ) Polynomial.X = 0 by
    simp [AdditiveGroup.counit]]
  exact map_one (ChevalleyRankOne.transvectionRoot ℤ i j hij)

private theorem rootAlgHom_counit_linear
    (i j : Fin 3) (hij : i ≠ j) :
    CoalgebraStruct.counit ∘ₗ (rootAlgHom i j hij).toLinearMap =
      CoalgebraStruct.counit := by
  change (AdditiveGroup.counit ℤ).toLinearMap ∘ₗ
      (rootAlgHom i j hij).toLinearMap =
    SpecialLinearThree.coordinateCounit.toLinearMap
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun (rootAlgHom_counit i j hij) x

private theorem rootAlgHom_comul_linear
    (i j : Fin 3) (hij : i ≠ j) :
    TensorProduct.map (rootAlgHom i j hij).toLinearMap
        (rootAlgHom i j hij).toLinearMap ∘ₗ
        CoalgebraStruct.comul =
      CoalgebraStruct.comul ∘ₗ (rootAlgHom i j hij).toLinearMap := by
  change TensorProduct.map (rootAlgHom i j hij).toLinearMap
      (rootAlgHom i j hij).toLinearMap ∘ₗ
      SpecialLinearThree.coordinateComul.toLinearMap =
    (AdditiveGroup.comul ℤ).toLinearMap ∘ₗ
      (rootAlgHom i j hij).toLinearMap
  apply LinearMap.ext
  intro x
  change (Algebra.TensorProduct.map (rootAlgHom i j hij)
      (rootAlgHom i j hij)) (SpecialLinearThree.coordinateComul x) =
    (AdditiveGroup.comul ℤ) ((rootAlgHom i j hij) x)
  exact DFunLike.congr_fun (rootAlgHom_comul i j hij) x

/-- The integral bialgebra morphism representing an elementary root subgroup
`Gₐ → SL₃`. -/
noncomputable def rootBialgHom
    (i j : Fin 3) (hij : i ≠ j) : A →ₐc[ℤ] P :=
  BialgHom.mk
    (CoalgHom.mk (rootAlgHom i j hij).toLinearMap
      (rootAlgHom_counit_linear i j hij)
      (rootAlgHom_comul_linear i j hij))
    (rootAlgHom i j hij).map_one
    (rootAlgHom i j hij).map_mul

theorem rootBialgHom_toAlgHom
    (i j : Fin 3) (hij : i ≠ j) :
    (rootBialgHom i j hij).toAlgHom = rootAlgHom i j hij := by
  apply AlgHom.ext
  intro x
  rfl

/-- Specializing at `t` recovers the usual transvection over every
commutative ring. -/
theorem rootBialgHom_specialization
    (i j : Fin 3) (hij : i ≠ j)
    {R : Type} [CommRing R] (t : R) :
    SpecialLinearThree.coordinateRingHomEquiv R
      ((Polynomial.aeval t).toRingHom.comp
        (rootBialgHom i j hij).toAlgHom.toRingHom) =
      ChevalleyRankOne.transvectionRoot R i j hij
        (Multiplicative.ofAdd t) := by
  change SpecialLinearThree.coordinateRingHomEquiv R
      ((Polynomial.aeval t).toRingHom.comp
        (rootAlgHom i j hij).toRingHom) = _
  change Matrix.SpecialLinearGroup.map
      ((Polynomial.aeval t).toRingHom.comp
        (rootAlgHom i j hij).toRingHom)
        SpecialLinearThree.universalPoint = _
  rw [SpecialLinearThree.specialLinearMap_comp_apply]
  rw [rootAlgHom_universal]
  rw [rootPoint_natural]
  simp

theorem rootBialgHom_specialization_injective
    (i j : Fin 3) (hij : i ≠ j)
    (R : Type) [CommRing R] :
    Function.Injective
      (fun t : R =>
        SpecialLinearThree.coordinateRingHomEquiv R
          ((Polynomial.aeval t).toRingHom.comp
            (rootBialgHom i j hij).toAlgHom.toRingHom)) := by
  intro x y hxy
  change SpecialLinearThree.coordinateRingHomEquiv R
      ((Polynomial.aeval x).toRingHom.comp
        (rootBialgHom i j hij).toAlgHom.toRingHom) =
    SpecialLinearThree.coordinateRingHomEquiv R
      ((Polynomial.aeval y).toRingHom.comp
        (rootBialgHom i j hij).toAlgHom.toRingHom) at hxy
  rw [rootBialgHom_specialization, rootBialgHom_specialization] at hxy
  have htag := ChevalleyRankOne.transvectionRoot_injective R i j hij hxy
  exact congrArg Multiplicative.toAdd htag

/-- Coordinate-Hopf map for the simple positive root `e₁-e₂`. -/
noncomputable def root12BialgHom : A →ₐc[ℤ] P :=
  rootBialgHom 0 1 (by decide)

/-- Coordinate-Hopf map for the simple positive root `e₂-e₃`. -/
noncomputable def root23BialgHom : A →ₐc[ℤ] P :=
  rootBialgHom 1 2 (by decide)

/-- Coordinate-Hopf map for the highest positive root `e₁-e₃`. -/
noncomputable def root13BialgHom : A →ₐc[ℤ] P :=
  rootBialgHom 0 2 (by decide)

theorem root12BialgHom_specialization
    {R : Type} [CommRing R] (t : R) :
    SpecialLinearThree.coordinateRingHomEquiv R
      ((Polynomial.aeval t).toRingHom.comp
        root12BialgHom.toAlgHom.toRingHom) =
      ChevalleyA2.root12 R (Multiplicative.ofAdd t) := by
  exact rootBialgHom_specialization 0 1 (by decide) t

theorem root23BialgHom_specialization
    {R : Type} [CommRing R] (t : R) :
    SpecialLinearThree.coordinateRingHomEquiv R
      ((Polynomial.aeval t).toRingHom.comp
        root23BialgHom.toAlgHom.toRingHom) =
      ChevalleyA2.root23 R (Multiplicative.ofAdd t) := by
  exact rootBialgHom_specialization 1 2 (by decide) t

theorem root13BialgHom_specialization
    {R : Type} [CommRing R] (t : R) :
    SpecialLinearThree.coordinateRingHomEquiv R
      ((Polynomial.aeval t).toRingHom.comp
        root13BialgHom.toAlgHom.toRingHom) =
      ChevalleyA2.root13 R (Multiplicative.ofAdd t) := by
  exact rootBialgHom_specialization 0 2 (by decide) t

/-- The affine group-scheme morphism `Gₐ → SL₃` induced by an elementary
root bialgebra morphism. -/
noncomputable def rootGroupSchemeHom
    (i j : Fin 3) (hij : i ≠ j) :
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj
      (Opposite.op (CommHopfAlgCat.of ℤ P))) ⟶
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj
      (Opposite.op (CommHopfAlgCat.of ℤ A))) :=
  (_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
    (CommHopfAlgCat.ofHom (rootBialgHom i j hij)).op

noncomputable def root12GroupSchemeHom :=
  rootGroupSchemeHom 0 1 (by decide)

noncomputable def root23GroupSchemeHom :=
  rootGroupSchemeHom 1 2 (by decide)

noncomputable def root13GroupSchemeHom :=
  rootGroupSchemeHom 0 2 (by decide)

end

end SpecialLinearThreeRootSubgroups
end AlgebraicGeometry
end RiemannResearch
