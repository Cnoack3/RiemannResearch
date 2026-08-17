/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.RingTheory.TensorProduct.Maps
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateTriality
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornSemilinearDescent

/-!
# Coordinate semilinear descent data for split-Zorn related triples

For a commutative extension L/K, an algebra automorphism of L and a D4
diagram symmetry act together on the scalar-extended coordinate algebra

    L ⊗[ℤ] RelatedTripleCoordinateRing.

The diagram automorphism used on the coordinate factor is already the
variance-corrected action: it is defined by pullback along the inverse diagram
symmetry. The tensor-factor formula proves that these equivalences form an
honest action, including for nonabelian S3 image.

Evaluation is then conjugated by the inverse total coordinate automorphism.
The resulting formula has coefficient automorphism followed by inverse
coordinate triality, and the representability theorem identifies it with the
previously constructed covariant semilinear action on universal related
triples.

This module constructs semilinear coordinate-algebra action data and its pointwise
representability formula. It does not construct a Cech module descent datum,
descend the Hopf operations, or assert representability of a fixed subgroup.

Source: user-provided D4 semilinear-triality program and inverse-variance
argument; the proofs are a formal synthesis of the existing coordinate
triality and universal point-functor naturality theorems.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

noncomputable section

universe u w

private abbrev A := RelatedTripleCoordinateRing.{0}

local instance coordinateSemilinearCommRing : CommRing A :=
  inferInstance

/-- Scalar extension of the integral related-triple coordinate algebra to a
commutative coefficient ring. -/
abbrev RelatedTripleCoordinateScalarExtension
    (L : Type u) [CommRing L] :=
  TensorProduct ℤ L A

/-- The coordinate-algebra semilinear equivalence attached to a coefficient
automorphism and a D4 diagram symmetry. -/
def relatedTripleCoordinateSemilinearEquiv
    (K : Type w) (L : Type u) [CommRing K] [CommRing L] [Algebra K L]
    (γ : L ≃ₐ[K] L) (σ : DiagramSymmetry) :
    RelatedTripleCoordinateScalarExtension L ≃ₐ[K]
      RelatedTripleCoordinateScalarExtension L :=
  Algebra.TensorProduct.congr γ
    (relatedTripleCoordinateOuterAlgEquiv σ)

@[simp] theorem relatedTripleCoordinateSemilinearEquiv_tmul
    (K : Type w) (L : Type u) [CommRing K] [CommRing L] [Algebra K L]
    (γ : L ≃ₐ[K] L) (σ : DiagramSymmetry) (l : L) (a : A) :
    relatedTripleCoordinateSemilinearEquiv K L γ σ (l ⊗ₜ[ℤ] a) =
      γ l ⊗ₜ[ℤ] relatedTripleCoordinateOuterAction σ a := by
  change
    (Algebra.TensorProduct.congr γ
      (relatedTripleCoordinateOuterAlgEquiv σ))
        (l ⊗ₜ[ℤ] a) =
      γ l ⊗ₜ[ℤ] relatedTripleCoordinateOuterAction σ a
  rw [Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  rfl

@[simp] theorem relatedTripleCoordinateSemilinearEquiv_symm_tmul
    (K : Type w) (L : Type u) [CommRing K] [CommRing L] [Algebra K L]
    (γ : L ≃ₐ[K] L) (σ : DiagramSymmetry) (l : L) (a : A) :
    (relatedTripleCoordinateSemilinearEquiv K L γ σ).symm
        (l ⊗ₜ[ℤ] a) =
      γ.symm l ⊗ₜ[ℤ] (relatedTripleCoordinateOuterAction σ).symm a := by
  change
    (Algebra.TensorProduct.congr γ
      (relatedTripleCoordinateOuterAlgEquiv σ)).symm
        (l ⊗ₜ[ℤ] a) =
      γ.symm l ⊗ₜ[ℤ] (relatedTripleCoordinateOuterAction σ).symm a
  rw [Algebra.TensorProduct.congr_symm_apply,
    Algebra.TensorProduct.map_tmul]
  rfl

/-- Algebra automorphisms of L/K, twisted by the D4 diagram homomorphism,
act on the scalar-extended coordinate algebra by K-algebra automorphisms. -/
def relatedTripleCoordinateSemilinearAction
    (K : Type w) (L : Type u) [CommRing K] [CommRing L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    (L ≃ₐ[K] L) →*
      AlgEquiv K (RelatedTripleCoordinateScalarExtension L)
        (RelatedTripleCoordinateScalarExtension L) where
  toFun γ :=
    relatedTripleCoordinateSemilinearEquiv K L γ (diagram γ)
  map_one' := by
    rw [diagram.map_one]
    apply AlgEquiv.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro l a
      rw [relatedTripleCoordinateSemilinearEquiv_tmul]
      have h := congrArg (fun e : A ≃ₐ[ℤ] A => e a)
        relatedTripleCoordinateOuterAlgAction.map_one
      exact congrArg (fun b => l ⊗ₜ[ℤ] b) h
    · intro x y hx hy
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  map_mul' γ δ := by
    rw [diagram.map_mul]
    apply AlgEquiv.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro l a
      simp only [AlgEquiv.mul_apply,
        relatedTripleCoordinateSemilinearEquiv_tmul]
      have h := congrArg (fun e : A ≃ₐ[ℤ] A => e a)
        (relatedTripleCoordinateOuterAlgAction.map_mul
          (diagram γ) (diagram δ))
      exact congrArg (fun b => γ (δ l) ⊗ₜ[ℤ] b) h
    · intro x y hx hy
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

@[simp] theorem relatedTripleCoordinateSemilinearAction_apply_tmul
    (K : Type w) (L : Type u) [CommRing K] [CommRing L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (γ : L ≃ₐ[K] L) (l : L) (a : A) :
    relatedTripleCoordinateSemilinearAction K L diagram γ
        (l ⊗ₜ[ℤ] a) =
      γ l ⊗ₜ[ℤ]
        relatedTripleCoordinateOuterAction (diagram γ) a :=
  relatedTripleCoordinateSemilinearEquiv_tmul K L γ (diagram γ) l a

/-- The coordinate action is semilinear for the left L-factor, written
multiplicatively inside the tensor-product algebra. -/
theorem relatedTripleCoordinateSemilinearAction_leftFactor_mul
    (K : Type w) (L : Type u) [CommRing K] [CommRing L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (γ : L ≃ₐ[K] L) (l : L)
    (b : RelatedTripleCoordinateScalarExtension L) :
    relatedTripleCoordinateSemilinearAction K L diagram γ
        (((l ⊗ₜ[ℤ] 1) :
          RelatedTripleCoordinateScalarExtension L) * b) =
      ((γ l ⊗ₜ[ℤ] 1) :
        RelatedTripleCoordinateScalarExtension L) *
        relatedTripleCoordinateSemilinearAction K L diagram γ b := by
  calc
    _ =
        relatedTripleCoordinateSemilinearAction K L diagram γ
            ((l ⊗ₜ[ℤ] 1) :
              RelatedTripleCoordinateScalarExtension L) *
          relatedTripleCoordinateSemilinearAction K L diagram γ b :=
      (relatedTripleCoordinateSemilinearAction K L diagram γ).map_mul _ _
    _ = _ := by
      rw [relatedTripleCoordinateSemilinearAction_apply_tmul]
      simp

/-- The underlying additive action is semilinear for the natural L-module
structure on the scalar-extended coordinate algebra. -/
theorem relatedTripleCoordinateSemilinearAction_smul
    (K : Type w) (L : Type u) [CommRing K] [CommRing L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (γ : L ≃ₐ[K] L) (l : L)
    (b : RelatedTripleCoordinateScalarExtension L) :
    relatedTripleCoordinateSemilinearAction K L diagram γ (l • b) =
      γ l • relatedTripleCoordinateSemilinearAction K L diagram γ b := by
  simp [Algebra.smul_def,
    relatedTripleCoordinateSemilinearAction_apply_tmul]

/-- Evaluation of the scalar-extended coordinate algebra at a represented
L-point. -/
def relatedTripleCoordinateScalarExtensionEvaluation
    (L : Type u) [CommRing L] (φ : A →+* L) :
    RelatedTripleCoordinateScalarExtension L →ₐ[L] L :=
  Algebra.TensorProduct.lift (AlgHom.id L L) φ.toIntAlgHom
    (fun l a => mul_comm l (φ a))

@[simp] theorem relatedTripleCoordinateScalarExtensionEvaluation_tmul
    (L : Type u) [CommRing L] (φ : A →+* L) (l : L) (a : A) :
    relatedTripleCoordinateScalarExtensionEvaluation L φ
        (l ⊗ₜ[ℤ] a) =
      l * φ a := by
  change
    (Algebra.TensorProduct.lift (AlgHom.id L L) φ.toIntAlgHom
      (fun l a => mul_comm l (φ a))) (l ⊗ₜ[ℤ] a) =
      l * φ a
  exact Algebra.TensorProduct.lift_tmul
    (AlgHom.id L L) φ.toIntAlgHom
      (fun l a => mul_comm l (φ a)) l a

/-- Conjugating evaluation by the coordinate semilinear equivalence produces
the coefficient-and-inverse-diagram transform of the represented point. -/
theorem relatedTripleCoordinateSemilinearEvaluation_conjugate
    (K : Type w) (L : Type u) [CommRing K] [CommRing L] [Algebra K L]
    (γ : L ≃ₐ[K] L) (σ : DiagramSymmetry) (φ : A →+* L) :
    γ.toRingEquiv.toRingHom.comp
        ((relatedTripleCoordinateScalarExtensionEvaluation L φ).toRingHom.comp
          (relatedTripleCoordinateSemilinearEquiv K L γ σ).symm.toRingEquiv.toRingHom) =
      (relatedTripleCoordinateScalarExtensionEvaluation L
        ((γ.toRingEquiv.toRingHom.comp φ).comp
          (relatedTripleCoordinateOuterAction σ⁻¹).toRingHom)).toRingHom := by
  apply RingHom.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    change γ ((relatedTripleCoordinateScalarExtensionEvaluation L φ)
        ((relatedTripleCoordinateSemilinearEquiv K L γ σ).symm
          (l ⊗ₜ[ℤ] a))) =
      l * γ (φ (relatedTripleCoordinateOuterAction σ⁻¹ a))
    rw [relatedTripleCoordinateSemilinearEquiv_symm_tmul,
      relatedTripleCoordinateScalarExtensionEvaluation_tmul]
    have h : (relatedTripleCoordinateOuterAction σ).symm a =
        relatedTripleCoordinateOuterAction σ⁻¹ a := by
      have hm := congrArg (fun e : RingAut A => e a)
        (relatedTripleCoordinateOuterAction.map_inv σ)
      exact hm.symm
    calc
      γ (γ.symm l *
          φ ((relatedTripleCoordinateOuterAction σ).symm a)) =
        γ (γ.symm l) *
          γ (φ ((relatedTripleCoordinateOuterAction σ).symm a)) :=
        γ.map_mul _ _
      _ = l * γ (φ ((relatedTripleCoordinateOuterAction σ).symm a)) := by
        rw [γ.apply_symm_apply]
      _ = l * γ (φ (relatedTripleCoordinateOuterAction σ⁻¹ a)) := by
        rw [h]
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Representability intertwines arbitrary scalar extension followed by
inverse coordinate triality with scalar extension followed by the covariant
universal point action. -/
theorem relatedTripleCoordinateRingHomEquiv_universalSemilinearNaturality
    {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (σ : DiagramSymmetry)
    (φ : RelatedTripleCoordinateRing.{0} →+* R) :
    coefficientRelatedTripleEquivUniversal S
      (relatedTripleCoordinateRingHomEquiv S
        ((f.comp φ).comp
          (relatedTripleCoordinateOuterAction σ⁻¹).toRingHom)) =
      universalRelatedTripleOuterAction S σ
        (universalRelatedTripleBaseChange f
          (coefficientRelatedTripleEquivUniversal R
            (relatedTripleCoordinateRingHomEquiv R φ))) := by
  rw [relatedTripleCoordinateRingHomEquiv_outerAction]
  rw [← relatedTripleCoordinateRingHomEquiv_naturality]
  apply Subtype.ext
  rfl

/-- The coordinate transform represented by the semilinear coordinate action
is exactly the existing algebra-automorphism semilinear action on universal
related triples. -/
theorem relatedTripleCoordinateRingHomEquiv_algebraAutSemilinearAction
    {K L : Type} [CommRing K] [CommRing L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (γ : L ≃ₐ[K] L)
    (φ : RelatedTripleCoordinateRing.{0} →+* L) :
    coefficientRelatedTripleEquivUniversal L
      (relatedTripleCoordinateRingHomEquiv L
        (((γ.toRingEquiv.toRingHom).comp φ).comp
          (relatedTripleCoordinateOuterAction (diagram γ)⁻¹).toRingHom)) =
      universalRelatedTripleAlgebraAutSemilinearAction K L diagram γ
        (coefficientRelatedTripleEquivUniversal L
          (relatedTripleCoordinateRingHomEquiv L φ)) :=
  relatedTripleCoordinateRingHomEquiv_universalSemilinearNaturality
    γ.toRingEquiv.toRingHom (diagram γ) φ

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
