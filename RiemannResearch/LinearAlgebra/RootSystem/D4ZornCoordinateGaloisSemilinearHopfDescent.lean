/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import RiemannResearch.GaloisCohomology.GaloisSemilinearAlgebraComonadicDescent
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateGaloisSemilinearAlgebraDescent

/-!
# Galois semilinear Hopf descent maps for D4 related triples

The coefficient-and-diagram Galois action on the scalar-extended D4
related-triple coordinate algebra preserves comultiplication, counit, and
antipode.  Consequently all three Hopf structure maps are morphisms of the
finite-Galois extension--restriction descent coalgebras.

This is the concrete Hopf-equivariance layer.  It does not yet identify the
resulting comonadic descent objects with the selected affine Čech objects or
construct the descended affine group scheme.

Source: user-provided D4 Hopf-descent program.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

noncomputable section

open RiemannResearch.GaloisCohomology
open scoped TensorProduct

universe u

private abbrev A := RelatedTripleCoordinateRing.{0}

local instance coordinateGaloisHopfCommRing : CommRing A :=
  inferInstance

/-- Base change along the variance-corrected coordinate action carries the
universal point to the inverse point symmetry. -/
theorem relatedTripleCoordinateOuterAction_universal
    (σ : DiagramSymmetry) :
    coefficientRelatedTripleBaseChange
        (relatedTripleCoordinateOuterAction σ).toRingHom
        universalCoefficientRelatedTriple =
      coefficientRelatedTripleOuterAction A σ⁻¹
        universalCoefficientRelatedTriple := by
  apply (relatedTripleCoordinateRingHomEquiv A).symm.injective
  change relatedTripleCoordinateEvaluation
      (coefficientRelatedTripleBaseChange
        (relatedTripleCoordinateOuterAction σ).toRingHom
        universalCoefficientRelatedTriple) =
    relatedTripleCoordinateEvaluation
      (coefficientRelatedTripleOuterAction A σ⁻¹
        universalCoefficientRelatedTriple)
  rw [relatedTripleCoordinateEvaluation_baseChange]
  have hu : relatedTripleCoordinateEvaluation
      universalCoefficientRelatedTriple = RingHom.id A := by
    rw [← relatedTripleCoordinateEvaluation_baseChange (RingHom.id A)]
    rw [DFunLike.congr_fun coefficientRelatedTripleBaseChange_id]
    rfl
  calc
    (relatedTripleCoordinateOuterAction σ).toRingHom =
        (relatedTripleCoordinateEvaluation universalCoefficientRelatedTriple).comp
          (relatedTripleCoordinateOuterAction σ).toRingHom := by rw [hu]; rfl
    _ = _ := relatedTripleCoordinateOuterAction_evaluation
      σ universalCoefficientRelatedTriple

/-- Triality preserves the integral coordinate antipode. -/
theorem relatedTripleCoordinateOuterAlgEquiv_antipode
    (σ : DiagramSymmetry) :
    (relatedTripleCoordinateOuterAlgEquiv σ).toAlgHom.comp
        relatedTripleCoordinateAntipode =
      relatedTripleCoordinateAntipode.comp
        (relatedTripleCoordinateOuterAlgEquiv σ).toAlgHom := by
  apply relatedTripleCoordinateAlgHom_ext
  change coefficientRelatedTripleBaseChange
      ((relatedTripleCoordinateOuterAlgEquiv σ).toRingEquiv.toRingHom.comp
        relatedTripleCoordinateAntipode.toRingHom)
        universalCoefficientRelatedTriple =
    coefficientRelatedTripleBaseChange
      (relatedTripleCoordinateAntipode.toRingHom.comp
        (relatedTripleCoordinateOuterAlgEquiv σ).toRingEquiv.toRingHom)
        universalCoefficientRelatedTriple
  rw [coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoordinateAntipode_universal]
  rw [map_inv]
  change (coefficientRelatedTripleBaseChange
      (relatedTripleCoordinateOuterAction σ).toRingHom
      universalCoefficientRelatedTriple)⁻¹ =
    coefficientRelatedTripleBaseChange
      (relatedTripleCoordinateAntipode.toRingHom.comp
        (relatedTripleCoordinateOuterAction σ).toRingHom)
      universalCoefficientRelatedTriple
  rw [relatedTripleCoordinateOuterAction_universal]
  rw [coefficientRelatedTripleBaseChange_comp_apply]
  rw [relatedTripleCoordinateOuterAction_universal]
  rw [coefficientRelatedTripleBaseChange_relabel]
  rw [relatedTripleCoordinateAntipode_universal]
  exact (coefficientRelatedTripleOuterAction A σ⁻¹).map_inv
    universalCoefficientRelatedTriple |>.symm

set_option maxHeartbeats 800000 in
-- The nested tensor interchanger induction is expensive to elaborate.
/-- The scalar-extended coordinate comultiplication is equivariant for the D4
coefficient-and-diagram action and its diagonal tensor-square action. -/
theorem relatedTripleCoordinateGaloisSemilinearComul_equivariant
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (γ : L ≃ₐ[K] L) (x : RelatedTripleCoordinateScalarExtension L) :
    (galoisSemilinearTensorSquareAction K L
      (RelatedTripleCoordinateScalarExtension L)
      (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram)).action γ
        (CoalgebraStruct.comul x) =
      CoalgebraStruct.comul
        ((relatedTripleCoordinateGaloisSemilinearAlgebraAction
          K L diagram).action γ x) := by
  set_option linter.style.setOption false in
  set_option synthInstance.maxHeartbeats 200000 in
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
      rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
      change _ = CoalgebraStruct.comul
        (relatedTripleCoordinateSemilinearAction K L diagram γ
          (l ⊗ₜ[ℤ] a))
      rw [relatedTripleCoordinateSemilinearAction_apply_tmul]
      rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
      have hnat (z : A ⊗[ℤ] A) :
          (galoisSemilinearTensorSquareAction K L
              (RelatedTripleCoordinateScalarExtension L)
              (relatedTripleCoordinateGaloisSemilinearAlgebraAction
                K L diagram)).action γ
            ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
              ℤ L ℤ L L L A A)
              ((1 ⊗ₜ[L] l) ⊗ₜ[ℤ] z)) =
            (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
              ℤ L ℤ L L L A A)
              ((1 ⊗ₜ[L] γ l) ⊗ₜ[ℤ]
                Algebra.TensorProduct.map
                  (relatedTripleCoordinateOuterAlgEquiv (diagram γ)).toAlgHom
                  (relatedTripleCoordinateOuterAlgEquiv (diagram γ)).toAlgHom z) := by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul b c =>
            rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
            rw [Algebra.TensorProduct.map_tmul]
            rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
            rw [galoisSemilinearTensorSquareAction_tmul]
            change
              relatedTripleCoordinateSemilinearAction K L diagram γ
                    (1 ⊗ₜ[ℤ] b) ⊗ₜ[L]
                  relatedTripleCoordinateSemilinearAction K L diagram γ
                    (l ⊗ₜ[ℤ] c) =
                (1 ⊗ₜ[ℤ]
                    relatedTripleCoordinateOuterAction (diagram γ) b) ⊗ₜ[L]
                  (γ l ⊗ₜ[ℤ]
                    relatedTripleCoordinateOuterAction (diagram γ) c)
            rw [relatedTripleCoordinateSemilinearAction_apply_tmul,
              relatedTripleCoordinateSemilinearAction_apply_tmul]
            simp
        | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]
      rw [hnat]
      have hcomul := congrArg
        (fun f : A →ₐ[ℤ] A ⊗[ℤ] A => f a)
        (relatedTripleCoordinateOuterAlgEquiv_comul (diagram γ))
      exact congrArg
        (fun z : A ⊗[ℤ] A =>
          (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
            ℤ L ℤ L L L A A)
            ((1 ⊗ₜ[L] γ l) ⊗ₜ[ℤ] z)) hcomul
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The scalar-extended coordinate counit is equivariant for the D4 action and
the scalar Galois action. -/
theorem relatedTripleCoordinateGaloisSemilinearCounit_equivariant
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (γ : L ≃ₐ[K] L) (x : RelatedTripleCoordinateScalarExtension L) :
    (galoisScalarSemilinearAlgebraAction K L).action γ
        (CoalgebraStruct.counit x) =
      CoalgebraStruct.counit
        ((relatedTripleCoordinateGaloisSemilinearAlgebraAction
          K L diagram).action γ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
      rw [TensorProduct.counit_tmul, CommSemiring.counit_apply]
      change _ = CoalgebraStruct.counit
        (relatedTripleCoordinateSemilinearAction K L diagram γ
          (l ⊗ₜ[ℤ] a))
      rw [relatedTripleCoordinateSemilinearAction_apply_tmul]
      rw [TensorProduct.counit_tmul, CommSemiring.counit_apply]
      have h := congrArg (fun f : A →ₐ[ℤ] ℤ => f a)
        (relatedTripleCoordinateOuterAlgEquiv_counit (diagram γ))
      change CoalgebraStruct.counit (R := ℤ)
          (relatedTripleCoordinateOuterAction (diagram γ) a) =
        CoalgebraStruct.counit (R := ℤ) a at h
      rw [h]
      exact map_zsmul γ (CoalgebraStruct.counit (R := ℤ) a) l
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The scalar-extended coordinate antipode is equivariant for the D4 action. -/
theorem relatedTripleCoordinateGaloisSemilinearAntipode_equivariant
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (γ : L ≃ₐ[K] L) (x : RelatedTripleCoordinateScalarExtension L) :
    (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram).action γ
        (HopfAlgebraStruct.antipode L x) =
      HopfAlgebraStruct.antipode L
        ((relatedTripleCoordinateGaloisSemilinearAlgebraAction
          K L diagram).action γ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
      rw [TensorProduct.antipode_def]
      rw [TensorProduct.AlgebraTensorModule.map_tmul]
      rw [CommSemiring.antipode_eq_id]
      change _ = HopfAlgebraStruct.antipode L
        (relatedTripleCoordinateSemilinearAction K L diagram γ
          (l ⊗ₜ[ℤ] a))
      rw [relatedTripleCoordinateSemilinearAction_apply_tmul]
      rw [TensorProduct.antipode_def]
      rw [TensorProduct.AlgebraTensorModule.map_tmul]
      rw [CommSemiring.antipode_eq_id]
      change relatedTripleCoordinateSemilinearAction K L diagram γ
          (l ⊗ₜ[ℤ] relatedTripleCoordinateAntipode a) =
        γ l ⊗ₜ[ℤ] relatedTripleCoordinateAntipode
          (relatedTripleCoordinateOuterAction (diagram γ) a)
      rw [relatedTripleCoordinateSemilinearAction_apply_tmul]
      have h := congrArg (fun f : A →ₐ[ℤ] A => f a)
        (relatedTripleCoordinateOuterAlgEquiv_antipode (diagram γ))
      exact congrArg (fun b : A => γ l ⊗ₜ[ℤ] b) h
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Coordinate comultiplication as a morphism of finite-Galois comonadic
descent data. -/
noncomputable def relatedTripleCoordinateGaloisSemilinearComulDescentMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    galoisSemilinearComonadicDescentData K L
        (RelatedTripleCoordinateScalarExtension L)
        ((relatedTripleCoordinateGaloisSemilinearAlgebraAction
          K L diagram).toModuleAction K L
            (RelatedTripleCoordinateScalarExtension L)) ⟶
      galoisSemilinearComonadicDescentData K L
        (TensorProduct L (RelatedTripleCoordinateScalarExtension L)
          (RelatedTripleCoordinateScalarExtension L))
        (galoisSemilinearTensorSquareAction K L
          (RelatedTripleCoordinateScalarExtension L)
          (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram)) :=
  galoisSemilinearComonadicDescentMap K L
    (RelatedTripleCoordinateScalarExtension L)
    (TensorProduct L (RelatedTripleCoordinateScalarExtension L)
      (RelatedTripleCoordinateScalarExtension L))
    ((relatedTripleCoordinateGaloisSemilinearAlgebraAction
      K L diagram).toModuleAction K L
        (RelatedTripleCoordinateScalarExtension L))
    (galoisSemilinearTensorSquareAction K L
      (RelatedTripleCoordinateScalarExtension L)
      (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram))
    CoalgebraStruct.comul
    (relatedTripleCoordinateGaloisSemilinearComul_equivariant K L diagram)

/-- Coordinate counit as a morphism of finite-Galois comonadic descent data. -/
noncomputable def relatedTripleCoordinateGaloisSemilinearCounitDescentMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    galoisSemilinearComonadicDescentData K L
        (RelatedTripleCoordinateScalarExtension L)
        ((relatedTripleCoordinateGaloisSemilinearAlgebraAction
          K L diagram).toModuleAction K L
            (RelatedTripleCoordinateScalarExtension L)) ⟶
      galoisSemilinearComonadicDescentData K L L
        ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L) :=
  galoisSemilinearComonadicDescentMap K L
    (RelatedTripleCoordinateScalarExtension L) L
    ((relatedTripleCoordinateGaloisSemilinearAlgebraAction
      K L diagram).toModuleAction K L
        (RelatedTripleCoordinateScalarExtension L))
    ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
    CoalgebraStruct.counit
    (relatedTripleCoordinateGaloisSemilinearCounit_equivariant K L diagram)

/-- Coordinate antipode as an endomorphism of finite-Galois comonadic descent
data. -/
noncomputable def relatedTripleCoordinateGaloisSemilinearAntipodeDescentMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    galoisSemilinearComonadicDescentData K L
        (RelatedTripleCoordinateScalarExtension L)
        ((relatedTripleCoordinateGaloisSemilinearAlgebraAction
          K L diagram).toModuleAction K L
            (RelatedTripleCoordinateScalarExtension L)) ⟶
      galoisSemilinearComonadicDescentData K L
        (RelatedTripleCoordinateScalarExtension L)
        ((relatedTripleCoordinateGaloisSemilinearAlgebraAction
          K L diagram).toModuleAction K L
            (RelatedTripleCoordinateScalarExtension L)) :=
  galoisSemilinearComonadicDescentMap K L
    (RelatedTripleCoordinateScalarExtension L)
    (RelatedTripleCoordinateScalarExtension L)
    ((relatedTripleCoordinateGaloisSemilinearAlgebraAction
      K L diagram).toModuleAction K L
        (RelatedTripleCoordinateScalarExtension L))
    ((relatedTripleCoordinateGaloisSemilinearAlgebraAction
      K L diagram).toModuleAction K L
        (RelatedTripleCoordinateScalarExtension L))
    (HopfAlgebraStruct.antipode L)
    (relatedTripleCoordinateGaloisSemilinearAntipode_equivariant K L diagram)

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
