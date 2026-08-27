/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AdditiveGroupScheme
import RiemannResearch.AlgebraicGeometry.ChevalleyRankOneRootSubgroups
import RiemannResearch.AlgebraicGeometry.SpecialLinearTwoCoordinateHopf

/-!
# Integral rank-one Chevalley root subgroup Hopf morphisms

This file constructs the coordinate-Hopf morphisms `O(SL₂) → ℤ[X]`
representing the positive and negative transvection root subgroups
`Gₐ → SL₂`. The maps preserve counit and comultiplication, specialize to the
usual transvection matrices over every commutative ring, and are passed
through Mathlib's `hopfSpec` to obtain affine group-scheme morphisms.

This rank-one construction does not yet construct split simply connected E8.
-/

open CategoryTheory
open scoped TensorProduct

namespace RiemannResearch
namespace AlgebraicGeometry
namespace SpecialLinearTwoRootSubgroups

noncomputable section

private abbrev A := SpecialLinearTwo.Coordinate
private abbrev P := AdditiveGroup.Coordinate ℤ
private abbrev T := A ⊗[ℤ] A
private abbrev Q := P ⊗[ℤ] P

local instance coordinateAddCommMonoid : AddCommMonoid A :=
  (inferInstance : Semiring A).toAddCommMonoid

local instance coordinateIntModule : Module ℤ A :=
  @Algebra.toModule ℤ A _ _ (inferInstance : Algebra ℤ A)

noncomputable local instance sourceTensorRing : Ring T :=
  SpecialLinearTwo.tensorProductRing

noncomputable local instance sourceTensorCommRing : CommRing T :=
  SpecialLinearTwo.tensorProductCommRing

local instance sourceTensorAlgebra : Algebra ℤ T :=
  @Algebra.TensorProduct.instAlgebra ℤ A A
    (inferInstance : CommSemiring ℤ)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)

noncomputable local instance sl2Hopf : HopfAlgebra ℤ A :=
  SpecialLinearTwo.coordinateHopfAlgebra

noncomputable local instance additiveHopf : HopfAlgebra ℤ P :=
  AdditiveGroup.hopfAlgebra ℤ

/-- The universal transvection point with polynomial parameter `X`. -/
def rootPoint (i j : Fin 2) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup (Fin 2) P :=
  ChevalleyRankOne.transvectionRoot P i j hij
    (Multiplicative.ofAdd (Polynomial.X : P))

/-- Pullback of functions along the universal transvection root subgroup. -/
def rootAlgHom (i j : Fin 2) (hij : i ≠ j) : A →ₐ[ℤ] P :=
  SpecialLinearTwo.coordinateAlgHomOfRingHom
    (SpecialLinearTwo.coordinateEvaluation (rootPoint i j hij))

@[simp] theorem rootAlgHom_quotient_X
    (i j : Fin 2) (hij : i ≠ j) (r s : Fin 2) :
    rootAlgHom i j hij
        (SpecialLinearTwo.quotient (MvPolynomial.X (r, s))) =
      Matrix.transvection i j (Polynomial.X : P) r s := by
  change SpecialLinearTwo.coordinateEvaluation (rootPoint i j hij)
      (SpecialLinearTwo.quotient (MvPolynomial.X (r, s))) = _
  rw [SpecialLinearTwo.coordinateEvaluation_quotient_X]
  rfl

theorem rootAlgHom_universal (i j : Fin 2) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.map (rootAlgHom i j hij).toRingHom
      SpecialLinearTwo.universalPoint = rootPoint i j hij := by
  change Matrix.SpecialLinearGroup.map
    (SpecialLinearTwo.coordinateEvaluation (rootPoint i j hij))
      SpecialLinearTwo.universalPoint = rootPoint i j hij
  exact SpecialLinearTwo.coordinateEvaluation_universal _

theorem rootPoint_natural
    (i j : Fin 2) (hij : i ≠ j)
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
    (i j : Fin 2) (hij : i ≠ j) :
    (Algebra.TensorProduct.map (rootAlgHom i j hij)
        (rootAlgHom i j hij)).toRingHom.comp
        SpecialLinearTwo.tensorIncludeLeft =
      additiveIncludeLeft.toRingHom.comp
        (rootAlgHom i j hij).toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [SpecialLinearTwo.tensorIncludeLeft, additiveIncludeLeft]

private theorem tensorMap_includeRight
    (i j : Fin 2) (hij : i ≠ j) :
    (Algebra.TensorProduct.map (rootAlgHom i j hij)
        (rootAlgHom i j hij)).toRingHom.comp
        SpecialLinearTwo.tensorIncludeRight =
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
    (i j : Fin 2) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.map
      (Algebra.TensorProduct.map (rootAlgHom i j hij)
        (rootAlgHom i j hij)).toRingHom
        SpecialLinearTwo.universalPointLeft =
      Matrix.SpecialLinearGroup.map additiveIncludeLeft.toRingHom
        (rootPoint i j hij) := by
  rw [SpecialLinearTwo.universalPointLeft]
  rw [← SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [tensorMap_includeLeft]
  rw [SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [rootAlgHom_universal]

private theorem tensorMap_universalPointRight
    (i j : Fin 2) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.map
      (Algebra.TensorProduct.map (rootAlgHom i j hij)
        (rootAlgHom i j hij)).toRingHom
        SpecialLinearTwo.universalPointRight =
      Matrix.SpecialLinearGroup.map additiveIncludeRight.toRingHom
        (rootPoint i j hij) := by
  rw [SpecialLinearTwo.universalPointRight]
  rw [← SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [tensorMap_includeRight]
  rw [SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [rootAlgHom_universal]

private theorem rootPoint_comul
    (i j : Fin 2) (hij : i ≠ j) :
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
    (i j : Fin 2) (hij : i ≠ j) :
    (Algebra.TensorProduct.map (rootAlgHom i j hij)
        (rootAlgHom i j hij)).comp
        SpecialLinearTwo.coordinateComul =
      (AdditiveGroup.comul ℤ).comp (rootAlgHom i j hij) := by
  apply SpecialLinearTwo.coordinateAlgHom_ext
  rw [SpecialLinearTwo.coordinateComul_baseChange]
  rw [tensorMap_universalPointLeft, tensorMap_universalPointRight]
  change _ = Matrix.SpecialLinearGroup.map
    ((AdditiveGroup.comul ℤ).toRingHom.comp
      (rootAlgHom i j hij).toRingHom)
      SpecialLinearTwo.universalPoint
  rw [SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [rootAlgHom_universal]
  exact rootPoint_comul i j hij

/-- The root pullback preserves the counit. -/
theorem rootAlgHom_counit
    (i j : Fin 2) (hij : i ≠ j) :
    (AdditiveGroup.counit ℤ).comp (rootAlgHom i j hij) =
      SpecialLinearTwo.coordinateCounit := by
  apply SpecialLinearTwo.coordinateAlgHom_ext
  change Matrix.SpecialLinearGroup.map
      ((AdditiveGroup.counit ℤ).toRingHom.comp
        (rootAlgHom i j hij).toRingHom)
        SpecialLinearTwo.universalPoint =
    Matrix.SpecialLinearGroup.map
      SpecialLinearTwo.coordinateCounit.toRingHom
        SpecialLinearTwo.universalPoint
  rw [SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [rootAlgHom_universal]
  rw [SpecialLinearTwo.coordinateCounit_universal]
  rw [rootPoint_natural]
  change ChevalleyRankOne.transvectionRoot ℤ i j hij
      (Multiplicative.ofAdd
        ((AdditiveGroup.counit ℤ) Polynomial.X)) = 1
  rw [show (AdditiveGroup.counit ℤ) Polynomial.X = 0 by
    simp [AdditiveGroup.counit]]
  exact map_one (ChevalleyRankOne.transvectionRoot ℤ i j hij)

private theorem rootAlgHom_counit_linear
    (i j : Fin 2) (hij : i ≠ j) :
    CoalgebraStruct.counit ∘ₗ (rootAlgHom i j hij).toLinearMap =
      CoalgebraStruct.counit := by
  change (AdditiveGroup.counit ℤ).toLinearMap ∘ₗ
      (rootAlgHom i j hij).toLinearMap =
    SpecialLinearTwo.coordinateCounit.toLinearMap
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun (rootAlgHom_counit i j hij) x

private theorem rootAlgHom_comul_linear
    (i j : Fin 2) (hij : i ≠ j) :
    TensorProduct.map (rootAlgHom i j hij).toLinearMap
        (rootAlgHom i j hij).toLinearMap ∘ₗ
        CoalgebraStruct.comul =
      CoalgebraStruct.comul ∘ₗ (rootAlgHom i j hij).toLinearMap := by
  change TensorProduct.map (rootAlgHom i j hij).toLinearMap
      (rootAlgHom i j hij).toLinearMap ∘ₗ
      SpecialLinearTwo.coordinateComul.toLinearMap =
    (AdditiveGroup.comul ℤ).toLinearMap ∘ₗ
      (rootAlgHom i j hij).toLinearMap
  apply LinearMap.ext
  intro x
  change (Algebra.TensorProduct.map (rootAlgHom i j hij)
      (rootAlgHom i j hij)) (SpecialLinearTwo.coordinateComul x) =
    (AdditiveGroup.comul ℤ) ((rootAlgHom i j hij) x)
  exact DFunLike.congr_fun (rootAlgHom_comul i j hij) x

/-- The integral bialgebra morphism representing the transvection root
subgroup `Gₐ → SL₂`. -/
noncomputable def rootBialgHom
    (i j : Fin 2) (hij : i ≠ j) : A →ₐc[ℤ] P :=
  BialgHom.mk
    (CoalgHom.mk (rootAlgHom i j hij).toLinearMap
      (rootAlgHom_counit_linear i j hij)
      (rootAlgHom_comul_linear i j hij))
    (rootAlgHom i j hij).map_one
    (rootAlgHom i j hij).map_mul

theorem rootBialgHom_toAlgHom
    (i j : Fin 2) (hij : i ≠ j) :
    (rootBialgHom i j hij).toAlgHom = rootAlgHom i j hij := by
  apply AlgHom.ext
  intro x
  rfl

/-- Specializing at `t` recovers the usual transvection matrix over every
commutative ring. -/
theorem rootBialgHom_specialization
    (i j : Fin 2) (hij : i ≠ j)
    {R : Type} [CommRing R] (t : R) :
    SpecialLinearTwo.coordinateRingHomEquiv R
      ((Polynomial.aeval t).toRingHom.comp
        (rootBialgHom i j hij).toAlgHom.toRingHom) =
      ChevalleyRankOne.transvectionRoot R i j hij
        (Multiplicative.ofAdd t) := by
  change SpecialLinearTwo.coordinateRingHomEquiv R
      ((Polynomial.aeval t).toRingHom.comp
        (rootAlgHom i j hij).toRingHom) = _
  change Matrix.SpecialLinearGroup.map
      ((Polynomial.aeval t).toRingHom.comp
        (rootAlgHom i j hij).toRingHom)
        SpecialLinearTwo.universalPoint = _
  rw [SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [rootAlgHom_universal]
  rw [rootPoint_natural]
  simp

theorem rootBialgHom_specialization_injective
    (i j : Fin 2) (hij : i ≠ j)
    (R : Type) [CommRing R] :
    Function.Injective
      (fun t : R =>
        SpecialLinearTwo.coordinateRingHomEquiv R
          ((Polynomial.aeval t).toRingHom.comp
            (rootBialgHom i j hij).toAlgHom.toRingHom)) := by
  intro x y hxy
  change SpecialLinearTwo.coordinateRingHomEquiv R
      ((Polynomial.aeval x).toRingHom.comp
        (rootBialgHom i j hij).toAlgHom.toRingHom) =
    SpecialLinearTwo.coordinateRingHomEquiv R
      ((Polynomial.aeval y).toRingHom.comp
        (rootBialgHom i j hij).toAlgHom.toRingHom) at hxy
  rw [rootBialgHom_specialization, rootBialgHom_specialization] at hxy
  have htag := ChevalleyRankOne.transvectionRoot_injective R i j hij hxy
  exact congrArg Multiplicative.toAdd htag

/-- Positive-root coordinate Hopf morphism
`a ↦ 1, b ↦ X, c ↦ 0, d ↦ 1`. -/
noncomputable def positiveBialgHom : A →ₐc[ℤ] P :=
  rootBialgHom 0 1 (by decide)

/-- Negative-root coordinate Hopf morphism
`a ↦ 1, b ↦ 0, c ↦ X, d ↦ 1`. -/
noncomputable def negativeBialgHom : A →ₐc[ℤ] P :=
  rootBialgHom 1 0 (by decide)

@[simp] theorem positiveBialgHom_a :
    positiveBialgHom
        (SpecialLinearTwo.quotient
          (MvPolynomial.X ((0 : Fin 2), (0 : Fin 2)))) = 1 := by
  change rootAlgHom 0 1 (by decide)
      (SpecialLinearTwo.quotient
        (MvPolynomial.X ((0 : Fin 2), (0 : Fin 2)))) = 1
  rw [rootAlgHom_quotient_X]
  simp [Matrix.transvection]

@[simp] theorem positiveBialgHom_b :
    positiveBialgHom
        (SpecialLinearTwo.quotient
          (MvPolynomial.X ((0 : Fin 2), (1 : Fin 2)))) =
      Polynomial.X := by
  change rootAlgHom 0 1 (by decide)
      (SpecialLinearTwo.quotient
        (MvPolynomial.X ((0 : Fin 2), (1 : Fin 2)))) = Polynomial.X
  rw [rootAlgHom_quotient_X]
  simp [Matrix.transvection]

@[simp] theorem positiveBialgHom_c :
    positiveBialgHom
        (SpecialLinearTwo.quotient
          (MvPolynomial.X ((1 : Fin 2), (0 : Fin 2)))) = 0 := by
  change rootAlgHom 0 1 (by decide)
      (SpecialLinearTwo.quotient
        (MvPolynomial.X ((1 : Fin 2), (0 : Fin 2)))) = 0
  rw [rootAlgHom_quotient_X]
  simp [Matrix.transvection]

@[simp] theorem positiveBialgHom_d :
    positiveBialgHom
        (SpecialLinearTwo.quotient
          (MvPolynomial.X ((1 : Fin 2), (1 : Fin 2)))) = 1 := by
  change rootAlgHom 0 1 (by decide)
      (SpecialLinearTwo.quotient
        (MvPolynomial.X ((1 : Fin 2), (1 : Fin 2)))) = 1
  rw [rootAlgHom_quotient_X]
  simp [Matrix.transvection]

@[simp] theorem negativeBialgHom_a :
    negativeBialgHom
        (SpecialLinearTwo.quotient
          (MvPolynomial.X ((0 : Fin 2), (0 : Fin 2)))) = 1 := by
  change rootAlgHom 1 0 (by decide)
      (SpecialLinearTwo.quotient
        (MvPolynomial.X ((0 : Fin 2), (0 : Fin 2)))) = 1
  rw [rootAlgHom_quotient_X]
  simp [Matrix.transvection]

@[simp] theorem negativeBialgHom_b :
    negativeBialgHom
        (SpecialLinearTwo.quotient
          (MvPolynomial.X ((0 : Fin 2), (1 : Fin 2)))) = 0 := by
  change rootAlgHom 1 0 (by decide)
      (SpecialLinearTwo.quotient
        (MvPolynomial.X ((0 : Fin 2), (1 : Fin 2)))) = 0
  rw [rootAlgHom_quotient_X]
  simp [Matrix.transvection]

@[simp] theorem negativeBialgHom_c :
    negativeBialgHom
        (SpecialLinearTwo.quotient
          (MvPolynomial.X ((1 : Fin 2), (0 : Fin 2)))) =
      Polynomial.X := by
  change rootAlgHom 1 0 (by decide)
      (SpecialLinearTwo.quotient
        (MvPolynomial.X ((1 : Fin 2), (0 : Fin 2)))) = Polynomial.X
  rw [rootAlgHom_quotient_X]
  simp [Matrix.transvection]

@[simp] theorem negativeBialgHom_d :
    negativeBialgHom
        (SpecialLinearTwo.quotient
          (MvPolynomial.X ((1 : Fin 2), (1 : Fin 2)))) = 1 := by
  change rootAlgHom 1 0 (by decide)
      (SpecialLinearTwo.quotient
        (MvPolynomial.X ((1 : Fin 2), (1 : Fin 2)))) = 1
  rw [rootAlgHom_quotient_X]
  simp [Matrix.transvection]

/-- The affine group-scheme morphism `Gₐ → SL₂` induced by a root bialgebra
morphism. -/
noncomputable def rootGroupSchemeHom
    (i j : Fin 2) (hij : i ≠ j) :
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj
      (Opposite.op (CommHopfAlgCat.of ℤ P))) ⟶
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj
      (Opposite.op (CommHopfAlgCat.of ℤ A))) :=
  (_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
    (CommHopfAlgCat.ofHom (rootBialgHom i j hij)).op

/-- Positive-root affine group-scheme morphism `Gₐ → SL₂`. -/
noncomputable def positiveRootGroupSchemeHom :=
  rootGroupSchemeHom 0 1 (by decide)

/-- Negative-root affine group-scheme morphism `Gₐ → SL₂`. -/
noncomputable def negativeRootGroupSchemeHom :=
  rootGroupSchemeHom 1 0 (by decide)

end

end SpecialLinearTwoRootSubgroups
end AlgebraicGeometry
end RiemannResearch
