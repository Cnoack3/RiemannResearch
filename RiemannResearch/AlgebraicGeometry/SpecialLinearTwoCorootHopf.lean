/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.MultiplicativeGroupScheme
import RiemannResearch.AlgebraicGeometry.SpecialLinearTwoRootSubgroupHopf

/-!
# The integral diagonal coroot of `SL₂`

This file constructs the genuine coordinate-Hopf morphism

`O(SL₂) → O(Gₘ) = ℤ[T, T⁻¹]`

corresponding contravariantly to the diagonal coroot

`u ↦ diag(u, u⁻¹)`.

The construction proves preservation of comultiplication and counit, packages
the resulting bialgebra morphism, identifies all four universal matrix
coordinates, proves specialization and injectivity over every commutative
ring, and obtains the affine group-scheme morphism `Gₘ → SL₂` via `hopfSpec`.

This completes the torus component of the integral rank-one pinning. It does
not yet construct the split simply connected E8 coordinate Hopf algebra.
-/

open CategoryTheory
open scoped TensorProduct

namespace RiemannResearch
namespace AlgebraicGeometry
namespace SpecialLinearTwoCoroot

noncomputable section

/-- The diagonal determinant-one point attached to a unit. -/
def diagonalPoint (S : Type) [CommRing S] (u : Sˣ) :
    Matrix.SpecialLinearGroup (Fin 2) S :=
  ⟨!![(u : S), 0; 0, (↑(u⁻¹) : S)], by
    rw [Matrix.det_fin_two]
    simp⟩

/-- The diagonal coroot is a homomorphism from units to `SL₂`. -/
noncomputable def diagonalCoroot (S : Type) [CommRing S] :
    Sˣ →* Matrix.SpecialLinearGroup (Fin 2) S where
  toFun := diagonalPoint S
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [diagonalPoint]
  map_mul' u v := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [diagonalPoint, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- The diagonal coroot commutes with arbitrary base change. -/
theorem diagonalCoroot_natural {S U : Type} [CommRing S] [CommRing U]
    (f : S →+* U) (u : Sˣ) :
    Matrix.SpecialLinearGroup.map f (diagonalCoroot S u) =
      diagonalCoroot U (Units.map f.toMonoidHom u) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change f (((diagonalCoroot S u : Matrix.SpecialLinearGroup (Fin 2) S) :
    Matrix (Fin 2) (Fin 2) S) i j) =
      (((diagonalCoroot U (Units.map f.toMonoidHom u) :
        Matrix.SpecialLinearGroup (Fin 2) U) :
          Matrix (Fin 2) (Fin 2) U) i j)
  fin_cases i <;> fin_cases j <;> simp [diagonalCoroot, diagonalPoint]

/-- The diagonal coroot is injective over every commutative ring. -/
theorem diagonalCoroot_injective (S : Type) [CommRing S] :
    Function.Injective (diagonalCoroot S) := by
  intro u v huv
  apply Units.ext
  have h00 := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) S =>
      ((g : Matrix (Fin 2) (Fin 2) S) 0 0)) huv
  simpa [diagonalCoroot, diagonalPoint] using h00

private abbrev A := SpecialLinearTwo.Coordinate
private abbrev L := MultiplicativeGroup.Coordinate ℤ
private abbrev T := A ⊗[ℤ] A
private abbrev Q := L ⊗[ℤ] L

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

noncomputable local instance gmHopf : HopfAlgebra ℤ L :=
  MultiplicativeGroup.hopfAlgebra ℤ

/-- Universal Laurent-polynomial coroot point. -/
def corootPoint : Matrix.SpecialLinearGroup (Fin 2) L :=
  diagonalCoroot L (MultiplicativeGroup.generatorUnit ℤ)

/-- Pullback of functions along the universal diagonal coroot. -/
def corootAlgHom : A →ₐ[ℤ] L :=
  SpecialLinearTwo.coordinateAlgHomOfRingHom
    (SpecialLinearTwo.coordinateEvaluation corootPoint)

theorem corootAlgHom_universal :
    Matrix.SpecialLinearGroup.map corootAlgHom.toRingHom
      SpecialLinearTwo.universalPoint = corootPoint := by
  change Matrix.SpecialLinearGroup.map
    (SpecialLinearTwo.coordinateEvaluation corootPoint)
      SpecialLinearTwo.universalPoint = corootPoint
  exact SpecialLinearTwo.coordinateEvaluation_universal _

theorem corootPoint_natural {R : Type} [CommRing R] (f : L →+* R) :
    Matrix.SpecialLinearGroup.map f corootPoint =
      diagonalCoroot R
        (Units.map f.toMonoidHom (MultiplicativeGroup.generatorUnit ℤ)) := by
  exact diagonalCoroot_natural f (MultiplicativeGroup.generatorUnit ℤ)

@[simp] theorem corootAlgHom_quotient_X (r s : Fin 2) :
    corootAlgHom (SpecialLinearTwo.quotient (MvPolynomial.X (r, s))) =
      ((corootPoint : Matrix.SpecialLinearGroup (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) r s := by
  change SpecialLinearTwo.coordinateEvaluation corootPoint
    (SpecialLinearTwo.quotient (MvPolynomial.X (r, s))) = _
  rw [SpecialLinearTwo.coordinateEvaluation_quotient_X]

private def gmIncludeLeft : L →ₐ[ℤ] Q :=
  Algebra.TensorProduct.includeLeft

private def gmIncludeRight : L →ₐ[ℤ] Q :=
  Algebra.TensorProduct.includeRight

private theorem tensorMap_includeLeft :
    (Algebra.TensorProduct.map corootAlgHom corootAlgHom).toRingHom.comp
        SpecialLinearTwo.tensorIncludeLeft =
      gmIncludeLeft.toRingHom.comp corootAlgHom.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  simp [SpecialLinearTwo.tensorIncludeLeft, gmIncludeLeft]

private theorem tensorMap_includeRight :
    (Algebra.TensorProduct.map corootAlgHom corootAlgHom).toRingHom.comp
        SpecialLinearTwo.tensorIncludeRight =
      gmIncludeRight.toRingHom.comp corootAlgHom.toRingHom := by
  apply DFunLike.ext _ _
  intro x
  change (Algebra.TensorProduct.map corootAlgHom corootAlgHom)
      ((1 : A) ⊗ₜ[ℤ] x) = (1 : L) ⊗ₜ[ℤ] corootAlgHom x
  rw [Algebra.TensorProduct.map_tmul]
  simp

private theorem tensorMap_universalPointLeft :
    Matrix.SpecialLinearGroup.map
      (Algebra.TensorProduct.map corootAlgHom corootAlgHom).toRingHom
        SpecialLinearTwo.universalPointLeft =
      Matrix.SpecialLinearGroup.map gmIncludeLeft.toRingHom corootPoint := by
  rw [SpecialLinearTwo.universalPointLeft]
  rw [← SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [tensorMap_includeLeft]
  rw [SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [corootAlgHom_universal]

private theorem tensorMap_universalPointRight :
    Matrix.SpecialLinearGroup.map
      (Algebra.TensorProduct.map corootAlgHom corootAlgHom).toRingHom
        SpecialLinearTwo.universalPointRight =
      Matrix.SpecialLinearGroup.map gmIncludeRight.toRingHom corootPoint := by
  rw [SpecialLinearTwo.universalPointRight]
  rw [← SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [tensorMap_includeRight]
  rw [SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [corootAlgHom_universal]

private theorem generatorUnit_comul :
    Units.map gmIncludeLeft.toRingHom.toMonoidHom
        (MultiplicativeGroup.generatorUnit ℤ) *
      Units.map gmIncludeRight.toRingHom.toMonoidHom
        (MultiplicativeGroup.generatorUnit ℤ) =
    Units.map (MultiplicativeGroup.comul ℤ).toRingHom.toMonoidHom
      (MultiplicativeGroup.generatorUnit ℤ) := by
  apply Units.ext
  change gmIncludeLeft (↑(MultiplicativeGroup.generatorUnit ℤ) : L) *
      gmIncludeRight (↑(MultiplicativeGroup.generatorUnit ℤ) : L) =
    MultiplicativeGroup.comul ℤ
      (↑(MultiplicativeGroup.generatorUnit ℤ) : L)
  rw [MultiplicativeGroup.coe_generatorUnit]
  change ((LaurentPolynomial.T 1 : L) ⊗ₜ[ℤ] (1 : L)) *
      ((1 : L) ⊗ₜ[ℤ] (LaurentPolynomial.T 1 : L)) =
    MultiplicativeGroup.comul ℤ (LaurentPolynomial.T 1)
  rw [show MultiplicativeGroup.comul ℤ (LaurentPolynomial.T 1) =
      (LaurentPolynomial.T 1 : L) ⊗ₜ[ℤ]
        (LaurentPolynomial.T 1 : L) by
    change CoalgebraStruct.comul (R := ℤ)
      (LaurentPolynomial.T (1 : ℤ) : L) = _
    exact MultiplicativeGroup.comul_T ℤ]
  simp

private theorem corootPoint_comul :
    Matrix.SpecialLinearGroup.map gmIncludeLeft.toRingHom corootPoint *
        Matrix.SpecialLinearGroup.map gmIncludeRight.toRingHom corootPoint =
      Matrix.SpecialLinearGroup.map
        (MultiplicativeGroup.comul ℤ).toRingHom corootPoint := by
  rw [corootPoint_natural, corootPoint_natural, corootPoint_natural]
  rw [← map_mul]
  rw [generatorUnit_comul]

private theorem generatorUnit_counit :
    Units.map (MultiplicativeGroup.counit ℤ).toRingHom.toMonoidHom
        (MultiplicativeGroup.generatorUnit ℤ) = 1 := by
  apply Units.ext
  change MultiplicativeGroup.counit ℤ
      (↑(MultiplicativeGroup.generatorUnit ℤ) : L) = 1
  rw [MultiplicativeGroup.coe_generatorUnit]
  change CoalgebraStruct.counit (R := ℤ)
      (LaurentPolynomial.T (1 : ℤ) : L) = 1
  exact MultiplicativeGroup.counit_T ℤ

private theorem corootPoint_counit :
    Matrix.SpecialLinearGroup.map
        (MultiplicativeGroup.counit ℤ).toRingHom corootPoint = 1 := by
  rw [corootPoint_natural]
  rw [generatorUnit_counit]
  exact map_one (diagonalCoroot ℤ)

/-- The coroot pullback preserves comultiplication. -/
theorem corootAlgHom_comul :
    (Algebra.TensorProduct.map corootAlgHom corootAlgHom).comp
        SpecialLinearTwo.coordinateComul =
      (MultiplicativeGroup.comul ℤ).comp corootAlgHom := by
  apply SpecialLinearTwo.coordinateAlgHom_ext
  rw [SpecialLinearTwo.coordinateComul_baseChange]
  rw [tensorMap_universalPointLeft, tensorMap_universalPointRight]
  change _ = Matrix.SpecialLinearGroup.map
    ((MultiplicativeGroup.comul ℤ).toRingHom.comp corootAlgHom.toRingHom)
      SpecialLinearTwo.universalPoint
  rw [SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [corootAlgHom_universal]
  exact corootPoint_comul

/-- The coroot pullback preserves the counit. -/
theorem corootAlgHom_counit :
    (MultiplicativeGroup.counit ℤ).comp corootAlgHom =
      SpecialLinearTwo.coordinateCounit := by
  apply SpecialLinearTwo.coordinateAlgHom_ext
  change Matrix.SpecialLinearGroup.map
      ((MultiplicativeGroup.counit ℤ).toRingHom.comp corootAlgHom.toRingHom)
        SpecialLinearTwo.universalPoint =
    Matrix.SpecialLinearGroup.map SpecialLinearTwo.coordinateCounit.toRingHom
      SpecialLinearTwo.universalPoint
  rw [SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [corootAlgHom_universal]
  rw [SpecialLinearTwo.coordinateCounit_universal]
  exact corootPoint_counit

private theorem corootAlgHom_counit_linear :
    CoalgebraStruct.counit ∘ₗ corootAlgHom.toLinearMap =
      CoalgebraStruct.counit := by
  change (MultiplicativeGroup.counit ℤ).toLinearMap ∘ₗ
      corootAlgHom.toLinearMap = SpecialLinearTwo.coordinateCounit.toLinearMap
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun corootAlgHom_counit x

private theorem corootAlgHom_comul_linear :
    TensorProduct.map corootAlgHom.toLinearMap corootAlgHom.toLinearMap ∘ₗ
        CoalgebraStruct.comul =
      CoalgebraStruct.comul ∘ₗ corootAlgHom.toLinearMap := by
  change TensorProduct.map corootAlgHom.toLinearMap corootAlgHom.toLinearMap ∘ₗ
      SpecialLinearTwo.coordinateComul.toLinearMap =
    (MultiplicativeGroup.comul ℤ).toLinearMap ∘ₗ corootAlgHom.toLinearMap
  apply LinearMap.ext
  intro x
  change (Algebra.TensorProduct.map corootAlgHom corootAlgHom)
      (SpecialLinearTwo.coordinateComul x) =
    MultiplicativeGroup.comul ℤ (corootAlgHom x)
  exact DFunLike.congr_fun corootAlgHom_comul x

/-- The integral coordinate bialgebra morphism representing `Gₘ → SL₂`. -/
noncomputable def corootBialgHom : A →ₐc[ℤ] L :=
  BialgHom.mk
    (CoalgHom.mk corootAlgHom.toLinearMap
      corootAlgHom_counit_linear corootAlgHom_comul_linear)
    corootAlgHom.map_one corootAlgHom.map_mul

theorem corootBialgHom_toAlgHom :
    corootBialgHom.toAlgHom = corootAlgHom := by
  apply AlgHom.ext
  intro x
  rfl

@[simp] theorem corootBialgHom_a :
    corootBialgHom
        (SpecialLinearTwo.quotient
          (MvPolynomial.X ((0 : Fin 2), (0 : Fin 2)))) =
      (LaurentPolynomial.T 1 : L) := by
  change corootAlgHom
      (SpecialLinearTwo.quotient
        (MvPolynomial.X ((0 : Fin 2), (0 : Fin 2)))) =
      (LaurentPolynomial.T 1 : L)
  rw [corootAlgHom_quotient_X]
  simp [corootPoint, diagonalCoroot, diagonalPoint]

@[simp] theorem corootBialgHom_b :
    corootBialgHom
        (SpecialLinearTwo.quotient
          (MvPolynomial.X ((0 : Fin 2), (1 : Fin 2)))) = 0 := by
  change corootAlgHom
      (SpecialLinearTwo.quotient
        (MvPolynomial.X ((0 : Fin 2), (1 : Fin 2)))) = 0
  rw [corootAlgHom_quotient_X]
  simp [corootPoint, diagonalCoroot, diagonalPoint]

@[simp] theorem corootBialgHom_c :
    corootBialgHom
        (SpecialLinearTwo.quotient
          (MvPolynomial.X ((1 : Fin 2), (0 : Fin 2)))) = 0 := by
  change corootAlgHom
      (SpecialLinearTwo.quotient
        (MvPolynomial.X ((1 : Fin 2), (0 : Fin 2)))) = 0
  rw [corootAlgHom_quotient_X]
  simp [corootPoint, diagonalCoroot, diagonalPoint]

@[simp] theorem corootBialgHom_d :
    corootBialgHom
        (SpecialLinearTwo.quotient
          (MvPolynomial.X ((1 : Fin 2), (1 : Fin 2)))) =
      (LaurentPolynomial.T (-1) : L) := by
  change corootAlgHom
      (SpecialLinearTwo.quotient
        (MvPolynomial.X ((1 : Fin 2), (1 : Fin 2)))) =
      (LaurentPolynomial.T (-1) : L)
  rw [corootAlgHom_quotient_X]
  exact MultiplicativeGroup.coe_generatorUnit_inv ℤ

/-- Specialization at a unit recovers the usual diagonal matrix. -/
theorem corootBialgHom_specialization
    {R : Type} [CommRing R] (u : Rˣ) :
    SpecialLinearTwo.coordinateRingHomEquiv R
      ((MultiplicativeGroup.evalAlgHom ℤ u).toRingHom.comp
        corootBialgHom.toAlgHom.toRingHom) =
      diagonalCoroot R u := by
  change SpecialLinearTwo.coordinateRingHomEquiv R
      ((MultiplicativeGroup.evalAlgHom ℤ u).toRingHom.comp
        corootAlgHom.toRingHom) = _
  change Matrix.SpecialLinearGroup.map
      ((MultiplicativeGroup.evalAlgHom ℤ u).toRingHom.comp
        corootAlgHom.toRingHom) SpecialLinearTwo.universalPoint = _
  rw [SpecialLinearTwo.specialLinearMap_comp_apply]
  rw [corootAlgHom_universal]
  rw [corootPoint_natural]
  congr 1
  apply Units.ext
  change MultiplicativeGroup.evalAlgHom ℤ u
      (↑(MultiplicativeGroup.generatorUnit ℤ) : L) = (u : R)
  rw [MultiplicativeGroup.coe_generatorUnit]
  rw [MultiplicativeGroup.evalAlgHom_T]
  simp

/-- The represented coroot is injective on points over every commutative ring. -/
theorem corootBialgHom_specialization_injective
    (R : Type) [CommRing R] :
    Function.Injective
      (fun u : Rˣ =>
        SpecialLinearTwo.coordinateRingHomEquiv R
          ((MultiplicativeGroup.evalAlgHom ℤ u).toRingHom.comp
            corootBialgHom.toAlgHom.toRingHom)) := by
  intro u v huv
  change SpecialLinearTwo.coordinateRingHomEquiv R
      ((MultiplicativeGroup.evalAlgHom ℤ u).toRingHom.comp
        corootBialgHom.toAlgHom.toRingHom) =
    SpecialLinearTwo.coordinateRingHomEquiv R
      ((MultiplicativeGroup.evalAlgHom ℤ v).toRingHom.comp
        corootBialgHom.toAlgHom.toRingHom) at huv
  rw [corootBialgHom_specialization, corootBialgHom_specialization] at huv
  exact diagonalCoroot_injective R huv

/-- The affine group-scheme coroot morphism `Gₘ → SL₂`. -/
noncomputable def corootGroupSchemeHom :
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj
      (Opposite.op (CommHopfAlgCat.of ℤ L))) ⟶
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj
      (Opposite.op (CommHopfAlgCat.of ℤ A))) :=
  (_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
    (CommHopfAlgCat.ofHom corootBialgHom).op

end

end SpecialLinearTwoCoroot
end AlgebraicGeometry
end RiemannResearch
