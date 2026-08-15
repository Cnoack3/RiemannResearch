/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.AlgebraicGeometry.Group.Affine
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateHopf

/-!
# Coordinate-ring triality for split-Zorn related triples

The finite-equation related-triple functor carries the corrected outer S₃
action. Representability transports it contravariantly to the coordinate
ring. This module makes the variance explicit: the raw pullback is an
antihomomorphism, and inserting σ⁻¹ gives an honest action by integral ring
automorphisms.

Point-evaluation compatibility and faithfulness are proved directly. The
faithfulness witness is the family of three integral matrix triples with one
component +1 and the other two components -1.

The same automorphisms preserve comultiplication and counit. They are packaged
as bialgebra equivalences and then as a faithful action by automorphisms of the
commutative Hopf algebra representing the related-triple group functor.

Source: user-provided hierarchy and inverse-variance argument. The proof is
an independent formal transport through the coordinate-ring universal
property.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

noncomputable section

private abbrev A := RelatedTripleCoordinateRing.{0}

local instance relatedTripleCoordinateCommRing : CommRing A :=
  inferInstance

/-- Pullback along a diagram symmetry, defined by evaluating at the image of
the universal related triple. -/
def relatedTripleCoordinatePullback (σ : DiagramSymmetry) : A →+* A :=
  @relatedTripleCoordinateEvaluation A relatedTripleCoordinateCommRing
    (@coefficientRelatedTripleOuterAction A relatedTripleCoordinateCommRing σ
      universalCoefficientRelatedTriple)

/-- The identity diagram symmetry induces the identity coordinate pullback. -/
@[simp] theorem relatedTripleCoordinatePullback_one :
    relatedTripleCoordinatePullback 1 = RingHom.id A := by
  apply (@relatedTripleCoordinateRingHomEquiv A
    relatedTripleCoordinateCommRing).injective
  change coefficientRelatedTripleBaseChange
      (relatedTripleCoordinatePullback 1) universalCoefficientRelatedTriple =
    coefficientRelatedTripleBaseChange (RingHom.id A)
      universalCoefficientRelatedTriple
  unfold relatedTripleCoordinatePullback
  rw [relatedTripleCoordinateEvaluation_universal]
  rw [DFunLike.congr_fun coefficientRelatedTripleBaseChange_id]
  exact DFunLike.congr_fun
    ((coefficientRelatedTripleOuterAction A).map_one)
    universalCoefficientRelatedTriple

/-- Coordinate pullback reverses multiplication, as required by
contravariance. -/
theorem relatedTripleCoordinatePullback_mul
    (σ τ : DiagramSymmetry) :
    relatedTripleCoordinatePullback (σ * τ) =
      (relatedTripleCoordinatePullback τ).comp
        (relatedTripleCoordinatePullback σ) := by
  apply (@relatedTripleCoordinateRingHomEquiv A
    relatedTripleCoordinateCommRing).injective
  change coefficientRelatedTripleBaseChange
      (relatedTripleCoordinatePullback (σ * τ))
        universalCoefficientRelatedTriple =
    coefficientRelatedTripleBaseChange
      ((relatedTripleCoordinatePullback τ).comp
        (relatedTripleCoordinatePullback σ))
      universalCoefficientRelatedTriple
  unfold relatedTripleCoordinatePullback
  rw [relatedTripleCoordinateEvaluation_universal]
  rw [coefficientRelatedTripleBaseChange_comp]
  change coefficientRelatedTripleOuterAction A (σ * τ)
      universalCoefficientRelatedTriple =
    coefficientRelatedTripleBaseChange
      (relatedTripleCoordinateEvaluation
        (coefficientRelatedTripleOuterAction A τ
          universalCoefficientRelatedTriple))
      (coefficientRelatedTripleBaseChange
        (relatedTripleCoordinateEvaluation
          (coefficientRelatedTripleOuterAction A σ
            universalCoefficientRelatedTriple))
        universalCoefficientRelatedTriple)
  rw [relatedTripleCoordinateEvaluation_universal]
  rw [coefficientRelatedTripleBaseChange_relabel]
  rw [relatedTripleCoordinateEvaluation_universal]
  exact DFunLike.congr_fun
    ((coefficientRelatedTripleOuterAction A).map_mul σ τ)
    universalCoefficientRelatedTriple

/-- Evaluating after raw pullback is the same as applying the symmetry to the
represented point. -/
theorem relatedTripleCoordinateEvaluation_comp_pullback
    {R : Type} [CommRing R]
    (σ : DiagramSymmetry) (g : coefficientRelatedTripleGroup R) :
    (relatedTripleCoordinateEvaluation g).comp
        (relatedTripleCoordinatePullback σ) =
      relatedTripleCoordinateEvaluation
        (coefficientRelatedTripleOuterAction R σ g) := by
  apply (relatedTripleCoordinateRingHomEquiv R).injective
  change coefficientRelatedTripleBaseChange
      ((relatedTripleCoordinateEvaluation g).comp
        (relatedTripleCoordinatePullback σ))
        universalCoefficientRelatedTriple =
    coefficientRelatedTripleBaseChange
      (relatedTripleCoordinateEvaluation
        (coefficientRelatedTripleOuterAction R σ g))
      universalCoefficientRelatedTriple
  rw [coefficientRelatedTripleBaseChange_comp]
  change coefficientRelatedTripleBaseChange
      (relatedTripleCoordinateEvaluation g)
      (coefficientRelatedTripleBaseChange
        (relatedTripleCoordinatePullback σ)
        universalCoefficientRelatedTriple) =
    coefficientRelatedTripleBaseChange
      (relatedTripleCoordinateEvaluation
        (coefficientRelatedTripleOuterAction R σ g))
      universalCoefficientRelatedTriple
  unfold relatedTripleCoordinatePullback
  rw [relatedTripleCoordinateEvaluation_universal]
  rw [coefficientRelatedTripleBaseChange_relabel]
  rw [relatedTripleCoordinateEvaluation_universal]
  rw [relatedTripleCoordinateEvaluation_universal]

/-- The covariant coordinate automorphism attached to σ. The inverse is
inserted because the raw coordinate pullback is contravariant. -/
def relatedTripleCoordinateOuterEquiv
    (σ : DiagramSymmetry) : RingAut A where
  toFun := relatedTripleCoordinatePullback σ⁻¹
  invFun := relatedTripleCoordinatePullback σ
  left_inv x := by
    have h := congrArg (fun f : A →+* A => f x)
      (relatedTripleCoordinatePullback_mul σ⁻¹ σ)
    simpa using h.symm
  right_inv x := by
    have h := congrArg (fun f : A →+* A => f x)
      (relatedTripleCoordinatePullback_mul σ σ⁻¹)
    simpa using h.symm
  map_mul' := (relatedTripleCoordinatePullback σ⁻¹).map_mul
  map_add' := (relatedTripleCoordinatePullback σ⁻¹).map_add

/-- The honest outer S₃ action on the integral coordinate algebra. -/
def relatedTripleCoordinateOuterAction :
    DiagramSymmetry →* RingAut A where
  toFun := relatedTripleCoordinateOuterEquiv
  map_one' := by
    apply RingEquiv.ext
    intro x
    simp [relatedTripleCoordinateOuterEquiv]
  map_mul' σ τ := by
    apply RingEquiv.ext
    intro x
    change relatedTripleCoordinatePullback (σ * τ)⁻¹ x =
      relatedTripleCoordinatePullback σ⁻¹
        (relatedTripleCoordinatePullback τ⁻¹ x)
    have h := congrArg (fun f : A →+* A => f x)
      (relatedTripleCoordinatePullback_mul τ⁻¹ σ⁻¹)
    simpa using h

/-- Under the honest coordinate action, point evaluation transforms by the
inverse point symmetry. -/
@[simp] theorem relatedTripleCoordinateOuterAction_evaluation
    {R : Type} [CommRing R]
    (σ : DiagramSymmetry) (g : coefficientRelatedTripleGroup R) :
    (relatedTripleCoordinateEvaluation g).comp
        (relatedTripleCoordinateOuterAction σ).toRingHom =
      relatedTripleCoordinateEvaluation
        (coefficientRelatedTripleOuterAction R σ⁻¹ g) := by
  exact relatedTripleCoordinateEvaluation_comp_pullback σ⁻¹ g

/-- Scalar extension sends the matrix unit -1 to -1. -/
@[simp] theorem coefficientRelatedTripleGLMap_neg_one
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    Matrix.GeneralLinearGroup.map f
      (-1 : Matrix.GeneralLinearGroup (Fin 8) R) = -1 := by
  apply Units.ext
  change (-(1 : Matrix (Fin 8) (Fin 8) R)).map f =
    -(1 : Matrix (Fin 8) (Fin 8) S)
  rw [Matrix.map_neg f (map_neg f),
    Matrix.map_one f (map_zero f) (map_one f)]

/-- The matrix unit -1 acts by negation on Zorn coordinates. -/
@[simp] theorem coefficientRelatedTripleMatrixApply_neg_one
    {R : Type} [CommRing R] (x : Octonion R) :
    matrixApply (-1 : Matrix.GeneralLinearGroup (Fin 8) R) x = -x := by
  change (-(1 : Matrix (Fin 8) (Fin 8) R)).mulVec x = -x
  rw [Matrix.neg_mulVec, Matrix.one_mulVec]

/-- An integral matrix tuple with sign +1 at i and sign -1 at the other two
labels. -/
def coefficientRelatedTripleCentralSignTuple
    (i : TrialityLabel) : MatrixTuple ℤ :=
  fun l => if l = i then 1 else -1

theorem coefficientRelatedTripleCentralSignTuple_mem_universal
    (i : TrialityLabel) :
    coefficientRelatedTripleCentralSignTuple i ∈
      universalRelatedTripleGroup ℤ := by
  constructor
  · intro l S _ f x
    by_cases h : l = i
    · simp [coefficientRelatedTripleCentralSignTuple, h, matrixApply]
    · simp [coefficientRelatedTripleCentralSignTuple, h, norm]
  · intro S _ f x
    cases i <;>
      simp [coefficientRelatedTripleCentralSignTuple, trialityEval,
        trialityTensor, normPolar, paraMul, mul, conjugate, norm,
        matrixTupleMap, coefficientRelatedTripleMatrixApply_neg_one] <;>
      ring

/-- The integral central-sign point in the finite-equation group. -/
def coefficientRelatedTripleCentralSignMarker (i : TrialityLabel) :
    coefficientRelatedTripleGroup ℤ :=
  ⟨coefficientRelatedTripleCentralSignTuple i,
    (satisfiesRelatedTripleCoefficientEquations_iff_mem_universal
      (coefficientRelatedTripleCentralSignTuple i)).2
      (coefficientRelatedTripleCentralSignTuple_mem_universal i)⟩

/-- Triality permutes the three integral central-sign points faithfully. -/
theorem coefficientRelatedTripleOuterAction_centralSignMarker
    (σ : DiagramSymmetry) (i : TrialityLabel) :
    coefficientRelatedTripleOuterAction ℤ σ
        (coefficientRelatedTripleCentralSignMarker i) =
      coefficientRelatedTripleCentralSignMarker (σ i) := by
  apply Subtype.ext
  funext l
  by_cases hσ : DiagramEven σ
  · simp [coefficientRelatedTripleOuterAction_apply_coe,
      coefficientRelatedTripleCentralSignMarker,
      coefficientRelatedTripleCentralSignTuple,
      matrixTupleTwistedRelabel, matrixTuplePureRelabel, hσ]
    simp only [Equiv.symm_apply_eq]
  · simp [coefficientRelatedTripleOuterAction_apply_coe,
      coefficientRelatedTripleCentralSignMarker,
      coefficientRelatedTripleCentralSignTuple,
      matrixTupleTwistedRelabel, matrixTuplePureRelabel,
      matrixTupleConjugation, hσ]
    simp only [Equiv.symm_apply_eq]

theorem coefficientRelatedTripleCentralSignMarker_injective :
    Function.Injective coefficientRelatedTripleCentralSignMarker := by
  intro i j h
  by_contra hij
  have hc := congrArg
    (fun g : coefficientRelatedTripleGroup ℤ =>
      (↑(g.1 i) : Matrix (Fin 8) (Fin 8) ℤ) 0 0) h
  simp [coefficientRelatedTripleCentralSignMarker,
    coefficientRelatedTripleCentralSignTuple, hij] at hc

/-- The pointwise outer action is faithful already on integral points. -/
theorem coefficientRelatedTripleOuterAction_injective_int :
    Function.Injective (coefficientRelatedTripleOuterAction ℤ) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  apply coefficientRelatedTripleCentralSignMarker_injective
  rw [← coefficientRelatedTripleOuterAction_centralSignMarker σ i,
    ← coefficientRelatedTripleOuterAction_centralSignMarker τ i]
  exact DFunLike.congr_fun h
    (coefficientRelatedTripleCentralSignMarker i)

/-- The induced outer S₃ action on the coordinate algebra is faithful. -/
theorem relatedTripleCoordinateOuterAction_injective :
    Function.Injective relatedTripleCoordinateOuterAction := by
  intro σ τ h
  have hpb :
      relatedTripleCoordinatePullback σ⁻¹ =
        relatedTripleCoordinatePullback τ⁻¹ := by
    change (relatedTripleCoordinateOuterAction σ).toRingHom =
      (relatedTripleCoordinateOuterAction τ).toRingHom
    rw [h]
  have ha :
      coefficientRelatedTripleOuterAction ℤ σ⁻¹ =
        coefficientRelatedTripleOuterAction ℤ τ⁻¹ := by
    apply MulEquiv.ext
    intro g
    apply (relatedTripleCoordinateRingHomEquiv ℤ).symm.injective
    change relatedTripleCoordinateEvaluation
        (coefficientRelatedTripleOuterAction ℤ σ⁻¹ g) =
      relatedTripleCoordinateEvaluation
        (coefficientRelatedTripleOuterAction ℤ τ⁻¹ g)
    rw [← relatedTripleCoordinateEvaluation_comp_pullback σ⁻¹ g,
      ← relatedTripleCoordinateEvaluation_comp_pullback τ⁻¹ g, hpb]
  have hi : σ⁻¹ = τ⁻¹ :=
    coefficientRelatedTripleOuterAction_injective_int ha
  simpa using congrArg Inv.inv hi

/-- The same automorphism, now over the coordinate ring's specified
integer-algebra structure. -/
def relatedTripleCoordinateOuterAlgEquiv
    (σ : DiagramSymmetry) : A ≃ₐ[ℤ] A :=
  AlgEquiv.ofRingEquiv (f := relatedTripleCoordinateOuterEquiv σ) (by
    intro z
    simp)

/-- The honest S₃ action by integer-algebra automorphisms. -/
def relatedTripleCoordinateOuterAlgAction :
    DiagramSymmetry →* (A ≃ₐ[ℤ] A) where
  toFun := relatedTripleCoordinateOuterAlgEquiv
  map_one' := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun relatedTripleCoordinateOuterAction.map_one x
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun
      (relatedTripleCoordinateOuterAction.map_mul σ τ) x

/-- The integer-algebra action is faithful. -/
theorem relatedTripleCoordinateOuterAlgAction_injective :
    Function.Injective relatedTripleCoordinateOuterAlgAction := by
  intro σ τ h
  apply relatedTripleCoordinateOuterAction_injective
  apply RingEquiv.ext
  intro x
  exact DFunLike.congr_fun h x

/-! ## Compatibility with the coordinate Hopf algebra -/

open CategoryTheory
open scoped TensorProduct

local instance relatedTripleTrialityCoordinateAddCommMonoid : AddCommMonoid A :=
  (inferInstance : Semiring A).toAddCommMonoid

local instance relatedTripleTrialityCoordinateIntModule : Module ℤ A :=
  @Algebra.toModule ℤ A _ _ (inferInstance : Algebra ℤ A)

private abbrev T := A ⊗[ℤ] A

noncomputable local instance relatedTripleTrialityTensorRing : Ring T :=
  relatedTripleTensorProductRing

noncomputable local instance relatedTripleTrialityTensorCommRing : CommRing T :=
  relatedTripleTensorProductCommRing

local instance relatedTripleTrialityTensorIntAlgebra : Algebra ℤ T :=
  @Algebra.TensorProduct.instAlgebra ℤ A A
    (inferInstance : CommSemiring ℤ)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)

private def relatedTripleOuterQ (σ : DiagramSymmetry) : A →ₐ[ℤ] A :=
  (relatedTripleCoordinateOuterAlgEquiv σ).toAlgHom

private def relatedTripleOuterQRing (σ : DiagramSymmetry) : A →+* A :=
  (relatedTripleCoordinateOuterAction σ).toRingHom

private def relatedTripleOuterQTensor (σ : DiagramSymmetry) : T →ₐ[ℤ] T :=
  Algebra.TensorProduct.map (relatedTripleOuterQ σ) (relatedTripleOuterQ σ)

private theorem relatedTripleCoordinateEvaluation_universal_id :
    relatedTripleCoordinateEvaluation (R := A)
        universalCoefficientRelatedTriple =
      RingHom.id A := by
  have h :=
    relatedTripleCoordinateEvaluation_baseChange (R := A) (RingHom.id A)
  rw [DFunLike.congr_fun coefficientRelatedTripleBaseChange_id
    universalCoefficientRelatedTriple] at h
  exact h

private theorem relatedTripleOuterQRing_universal
    (σ : DiagramSymmetry) :
    coefficientRelatedTripleBaseChange (relatedTripleOuterQRing σ)
        universalCoefficientRelatedTriple =
      coefficientRelatedTripleOuterAction A σ⁻¹
        universalCoefficientRelatedTriple := by
  apply (relatedTripleCoordinateRingHomEquiv A).symm.injective
  change relatedTripleCoordinateEvaluation
      (coefficientRelatedTripleBaseChange (relatedTripleOuterQRing σ)
        universalCoefficientRelatedTriple) =
    relatedTripleCoordinateEvaluation
      (coefficientRelatedTripleOuterAction A σ⁻¹
        universalCoefficientRelatedTriple)
  rw [relatedTripleCoordinateEvaluation_baseChange]
  have h :=
    relatedTripleCoordinateOuterAction_evaluation
      σ universalCoefficientRelatedTriple
  rw [relatedTripleCoordinateEvaluation_universal_id] at h
  exact h

private theorem relatedTripleOuterQTensor_left (σ : DiagramSymmetry) :
    (relatedTripleOuterQTensor σ).toRingHom.comp
        relatedTripleTensorIncludeLeft =
      relatedTripleTensorIncludeLeft.comp
        (relatedTripleOuterQRing σ) := by
  apply DFunLike.ext _ _
  intro x
  change Algebra.TensorProduct.map
      (relatedTripleOuterQ σ) (relatedTripleOuterQ σ)
      (x ⊗ₜ[ℤ] (1 : A)) =
    ((relatedTripleOuterQ σ) x) ⊗ₜ[ℤ] (1 : A)
  rw [Algebra.TensorProduct.map_tmul, map_one]

private theorem relatedTripleOuterQTensor_right (σ : DiagramSymmetry) :
    (relatedTripleOuterQTensor σ).toRingHom.comp
        relatedTripleTensorIncludeRight =
      relatedTripleTensorIncludeRight.comp
        (relatedTripleOuterQRing σ) := by
  apply DFunLike.ext _ _
  intro x
  change Algebra.TensorProduct.map
      (relatedTripleOuterQ σ) (relatedTripleOuterQ σ)
      ((1 : A) ⊗ₜ[ℤ] x) =
    (1 : A) ⊗ₜ[ℤ] ((relatedTripleOuterQ σ) x)
  rw [Algebra.TensorProduct.map_tmul, map_one]

private theorem relatedTripleOuterQTensor_leftPoint
    (σ : DiagramSymmetry) :
    coefficientRelatedTripleBaseChange
        (relatedTripleOuterQTensor σ).toRingHom
        universalCoefficientRelatedTripleLeft =
      coefficientRelatedTripleOuterAction T σ⁻¹
        universalCoefficientRelatedTripleLeft := by
  unfold universalCoefficientRelatedTripleLeft
  rw [← coefficientRelatedTripleBaseChange_comp_apply
    relatedTripleTensorIncludeLeft
    (relatedTripleOuterQTensor σ).toRingHom
    universalCoefficientRelatedTriple]
  rw [relatedTripleOuterQTensor_left]
  rw [coefficientRelatedTripleBaseChange_comp_apply
    (R := A) (S := A) (U := T)
    (relatedTripleOuterQRing σ) relatedTripleTensorIncludeLeft
    universalCoefficientRelatedTriple]
  rw [relatedTripleOuterQRing_universal]
  exact coefficientRelatedTripleBaseChange_relabel
    relatedTripleTensorIncludeLeft σ⁻¹ universalCoefficientRelatedTriple

private theorem relatedTripleOuterQTensor_rightPoint
    (σ : DiagramSymmetry) :
    coefficientRelatedTripleBaseChange
        (relatedTripleOuterQTensor σ).toRingHom
        universalCoefficientRelatedTripleRight =
      coefficientRelatedTripleOuterAction T σ⁻¹
        universalCoefficientRelatedTripleRight := by
  unfold universalCoefficientRelatedTripleRight
  rw [← coefficientRelatedTripleBaseChange_comp_apply
    relatedTripleTensorIncludeRight
    (relatedTripleOuterQTensor σ).toRingHom
    universalCoefficientRelatedTriple]
  rw [relatedTripleOuterQTensor_right]
  rw [coefficientRelatedTripleBaseChange_comp_apply
    (R := A) (S := A) (U := T)
    (relatedTripleOuterQRing σ) relatedTripleTensorIncludeRight
    universalCoefficientRelatedTriple]
  rw [relatedTripleOuterQRing_universal]
  exact coefficientRelatedTripleBaseChange_relabel
    relatedTripleTensorIncludeRight σ⁻¹ universalCoefficientRelatedTriple

/-- Triality preserves coordinate comultiplication. -/
theorem relatedTripleCoordinateOuterAlgEquiv_comul
    (σ : DiagramSymmetry) :
    (Algebra.TensorProduct.map
        (relatedTripleOuterQ σ) (relatedTripleOuterQ σ)).comp
          (Bialgebra.comulAlgHom ℤ A) =
      (Bialgebra.comulAlgHom ℤ A).comp
        (relatedTripleOuterQ σ) := by
  change (relatedTripleOuterQTensor σ).comp
      relatedTripleCoordinateComul =
    relatedTripleCoordinateComul.comp (relatedTripleOuterQ σ)
  apply relatedTripleCoordinateAlgHom_ext
  rw [relatedTripleCoordinateComul_baseChange]
  rw [relatedTripleOuterQTensor_leftPoint,
    relatedTripleOuterQTensor_rightPoint]
  rw [← (coefficientRelatedTripleOuterAction T σ⁻¹).map_mul]
  change coefficientRelatedTripleOuterAction T σ⁻¹
      (universalCoefficientRelatedTripleLeft *
        universalCoefficientRelatedTripleRight) =
    coefficientRelatedTripleBaseChange
      (relatedTripleCoordinateComul.toRingHom.comp
        (relatedTripleOuterQ σ).toRingHom)
      universalCoefficientRelatedTriple
  rw [show (relatedTripleOuterQ σ).toRingHom =
    relatedTripleOuterQRing σ from rfl]
  rw [coefficientRelatedTripleBaseChange_comp_apply
    (R := A) (S := A) (U := T)
    (relatedTripleOuterQRing σ)
    relatedTripleCoordinateComul.toRingHom
    universalCoefficientRelatedTriple]
  rw [relatedTripleOuterQRing_universal]
  rw [coefficientRelatedTripleBaseChange_relabel]
  rw [relatedTripleCoordinateComul_universal]
  rfl

/-- Triality preserves the coordinate counit. -/
theorem relatedTripleCoordinateOuterAlgEquiv_counit
    (σ : DiagramSymmetry) :
    (Bialgebra.counitAlgHom ℤ A).comp (relatedTripleOuterQ σ) =
      Bialgebra.counitAlgHom ℤ A := by
  change relatedTripleCoordinateCounit.comp (relatedTripleOuterQ σ) =
    relatedTripleCoordinateCounit
  apply relatedTripleCoordinateAlgHom_ext
  change coefficientRelatedTripleBaseChange
      (relatedTripleCoordinateCounit.toRingHom.comp
        (relatedTripleOuterQ σ).toRingHom)
      universalCoefficientRelatedTriple =
    coefficientRelatedTripleBaseChange
      relatedTripleCoordinateCounit.toRingHom
      universalCoefficientRelatedTriple
  rw [show (relatedTripleOuterQ σ).toRingHom =
    relatedTripleOuterQRing σ from rfl]
  rw [coefficientRelatedTripleBaseChange_comp_apply
    (R := A) (S := A) (U := ℤ)
    (relatedTripleOuterQRing σ)
    relatedTripleCoordinateCounit.toRingHom
    universalCoefficientRelatedTriple]
  rw [relatedTripleOuterQRing_universal]
  rw [coefficientRelatedTripleBaseChange_relabel]
  rw [relatedTripleCoordinateCounit_universal]
  exact map_one (coefficientRelatedTripleOuterAction ℤ σ⁻¹)

/-- Triality as a bialgebra equivalence of the coordinate Hopf algebra. -/
noncomputable def relatedTripleCoordinateOuterBialgEquiv
    (σ : DiagramSymmetry) : A ≃ₐc[ℤ] A :=
  BialgEquiv.ofAlgEquiv
    (relatedTripleCoordinateOuterAlgEquiv σ)
    (relatedTripleCoordinateOuterAlgEquiv_counit σ)
    (relatedTripleCoordinateOuterAlgEquiv_comul σ)

/-- One triality symmetry as an automorphism in the category of commutative
Hopf algebras. -/
noncomputable def relatedTripleCoordinateOuterHopfAut
    (σ : DiagramSymmetry) :
    CategoryTheory.Aut (CommHopfAlgCat.of ℤ A) :=
  CommHopfAlgCat.isoMk (relatedTripleCoordinateOuterBialgEquiv σ)

/-- The honest outer S₃ action by automorphisms of the commutative coordinate
Hopf algebra. -/
noncomputable def relatedTripleCoordinateOuterHopfAction :
    DiagramSymmetry →*
      CategoryTheory.Aut (CommHopfAlgCat.of ℤ A) where
  toFun := relatedTripleCoordinateOuterHopfAut
  map_one' := by
    apply CategoryTheory.Iso.ext
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.ext
    intro x
    change relatedTripleCoordinateOuterAlgEquiv 1 x = x
    exact DFunLike.congr_fun
      relatedTripleCoordinateOuterAlgAction.map_one x
  map_mul' σ τ := by
    apply CategoryTheory.Iso.ext
    apply CommHopfAlgCat.hom_ext
    apply BialgHom.ext
    intro x
    change relatedTripleCoordinateOuterAlgEquiv (σ * τ) x =
      relatedTripleCoordinateOuterAlgEquiv σ
        (relatedTripleCoordinateOuterAlgEquiv τ x)
    exact DFunLike.congr_fun
      (relatedTripleCoordinateOuterAlgAction.map_mul σ τ) x

/-- The outer S₃ action on the coordinate Hopf algebra is faithful. -/
theorem relatedTripleCoordinateOuterHopfAction_injective :
    Function.Injective relatedTripleCoordinateOuterHopfAction := by
  intro σ τ h
  apply relatedTripleCoordinateOuterAlgAction_injective
  apply AlgEquiv.ext
  intro x
  have hh := congrArg CategoryTheory.Iso.hom h
  have hb := congrArg CommHopfAlgCat.Hom.hom hh
  exact DFunLike.congr_fun hb x

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
