/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateRing

/-!
# Coordinate-cogroup maps for split-Zorn related triples

The represented coefficient-related-triple functor is group-valued.  This
module constructs the corresponding maps on its integral coordinate algebra:
comultiplication from the product of two universal points, counit from the
identity, and coinverse from the inverse universal point.

The tensor product needs a coherence bridge: we pin the quotient algebra's
additive and module structures, then combine Mathlib's tensor-product semiring
and additive-group structures into a commutative ring.  No mathematical
assumption is added.

We use the canonical small instance `RelatedTripleCoordinateRing.{0}`.
The current evaluation and base-change API requires source and target rings in
one universe; this specialization is what makes the integral counit an honest
map to `ℤ`.  A universe-polymorphic version would first require cross-universe
base change.

The universal-point equations below kernel-check the meaning of all three
maps. This module deliberately stops before installing a `HopfAlgebra`
instance. The downstream module `D4ZornCoordinateHopf` transports the
cogroup laws through Mathlib's dependent tensor associators, proves both
counit laws, coassociativity, and both antipode laws, and installs the
bialgebra and Hopf-algebra instances.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

noncomputable section

open scoped TensorProduct

private abbrev A := RelatedTripleCoordinateRing.{0}
private abbrev T := (A ⊗[ℤ] A)

local instance relatedTripleCoordinateAddCommMonoid : AddCommMonoid A :=
  (inferInstance : Semiring A).toAddCommMonoid

local instance relatedTripleCoordinateIntModule : Module ℤ A :=
  @Algebra.toModule ℤ A _ _
    (inferInstance : Algebra ℤ A)

/-- The ring structure on the tensor square of the coordinate algebra. -/
@[instance_reducible] noncomputable def relatedTripleTensorProductRing :
    Ring T := by
  let sr : Semiring T := inferInstance
  let ag : AddCommGroup T := inferInstance
  exact { sr, ag with
    intCast := Int.castDef
    intCast_ofNat := by intro n; rfl
    intCast_negSucc := by intro n; rfl }

noncomputable local instance : Ring T :=
  relatedTripleTensorProductRing

/-- The commutative-ring structure on the tensor square. -/
@[instance_reducible] noncomputable def relatedTripleTensorProductCommRing :
    CommRing T := by
  let cr : CommSemiring T :=
    Algebra.TensorProduct.instCommSemiring
  exact { relatedTripleTensorProductRing, cr with }

noncomputable local instance : CommRing T :=
  relatedTripleTensorProductCommRing

local instance relatedTripleTensorCanonicalIntAlgebra : Algebra ℤ T :=
  @Algebra.TensorProduct.instAlgebra ℤ A A
    (inferInstance : CommSemiring ℤ)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)
    (inferInstance : Semiring A)
    (inferInstance : Algebra ℤ A)

/-- Package a coordinate-ring morphism as an integer algebra morphism. -/
def relatedTripleCoordinateAlgHomOfRingHom
    {R : Type} [CommRing R] [Algebra ℤ R]
    (f : A →+* R) : A →ₐ[ℤ] R where
  toRingHom := f
  commutes' z := by simp

/-- Inclusion of the first tensor factor. -/
def relatedTripleTensorIncludeLeft : A →+* T :=
  Algebra.TensorProduct.includeLeftRingHom

/-- Inclusion of the second tensor factor. -/
def relatedTripleTensorIncludeRight : A →+* T where
  toFun x := (1 : A) ⊗ₜ[ℤ] x
  map_one' := by
    exact (Algebra.TensorProduct.one_def :
      (1 : T) = (1 : A) ⊗ₜ[ℤ] (1 : A)).symm
  map_mul' x y := by
    have h :
        ((1 : A) ⊗ₜ[ℤ] x) * ((1 : A) ⊗ₜ[ℤ] y) =
          ((1 : A) * 1) ⊗ₜ[ℤ] (x * y) :=
      Algebra.TensorProduct.tmul_mul_tmul _ _ _ _
    rw [show (1 : A) * 1 = 1 by exact mul_one (1 : A)] at h
    exact h.symm
  map_zero' := TensorProduct.tmul_zero A (1 : A)
  map_add' x y := TensorProduct.tmul_add (1 : A) x y

/-- The universal point in the left tensor factor. -/
def universalCoefficientRelatedTripleLeft :
    coefficientRelatedTripleGroup T :=
  coefficientRelatedTripleBaseChange relatedTripleTensorIncludeLeft
    universalCoefficientRelatedTriple

/-- The universal point in the right tensor factor. -/
def universalCoefficientRelatedTripleRight :
    coefficientRelatedTripleGroup T :=
  coefficientRelatedTripleBaseChange relatedTripleTensorIncludeRight
    universalCoefficientRelatedTriple

set_option synthInstance.maxHeartbeats 200000 in
-- Subgroup multiplication needs a larger typeclass-inference budget.
/-- The product of the two universal tensor-factor points.

The scoped heartbeat allowance covers inference of the subgroup multiplication. -/
def universalCoefficientRelatedTripleProduct :
    coefficientRelatedTripleGroup T :=
  universalCoefficientRelatedTripleLeft *
    universalCoefficientRelatedTripleRight

set_option linter.checkUnivs false in
/-- Coordinate comultiplication. -/
def relatedTripleCoordinateComul : A →ₐ[ℤ] T :=
  relatedTripleCoordinateAlgHomOfRingHom
    (relatedTripleCoordinateEvaluation
      universalCoefficientRelatedTripleProduct)

/-- Coordinate counit. -/
def relatedTripleCoordinateCounit : A →ₐ[ℤ] ℤ :=
  relatedTripleCoordinateAlgHomOfRingHom
    (relatedTripleCoordinateEvaluation
      (R := ℤ) (1 : coefficientRelatedTripleGroup ℤ))

/-- Coordinate coinverse. -/
def relatedTripleCoordinateAntipode : A →ₐ[ℤ] A :=
  relatedTripleCoordinateAlgHomOfRingHom
    (relatedTripleCoordinateEvaluation
      universalCoefficientRelatedTriple⁻¹)

set_option maxHeartbeats 800000 in
-- Coordinate evaluation reduces through the tensor coherence bridge.
/-- Comultiplication sends the universal point to the universal product.

The scoped heartbeat allowance covers reduction through coordinate evaluation
and the tensor coherence bridge. -/
theorem relatedTripleCoordinateComul_universal :
    coefficientRelatedTripleBaseChange
        (R := A) (S := T)
        relatedTripleCoordinateComul.toRingHom
        universalCoefficientRelatedTriple =
      universalCoefficientRelatedTripleProduct := by
  change coefficientRelatedTripleBaseChange
    (relatedTripleCoordinateEvaluation
      (R := T) universalCoefficientRelatedTripleProduct)
    universalCoefficientRelatedTriple =
      universalCoefficientRelatedTripleProduct
  exact relatedTripleCoordinateEvaluation_universal
    (R := T) universalCoefficientRelatedTripleProduct

/-- Counit sends the universal point to the identity. -/
theorem relatedTripleCoordinateCounit_universal :
    coefficientRelatedTripleBaseChange
        (R := A) (S := ℤ)
        relatedTripleCoordinateCounit.toRingHom
        universalCoefficientRelatedTriple = 1 := by
  change coefficientRelatedTripleBaseChange
    (relatedTripleCoordinateEvaluation
      (R := ℤ) (1 : coefficientRelatedTripleGroup ℤ))
    universalCoefficientRelatedTriple = 1
  exact relatedTripleCoordinateEvaluation_universal
    (R := ℤ) (1 : coefficientRelatedTripleGroup ℤ)

/-- Coinverse sends the universal point to its group inverse. -/
theorem relatedTripleCoordinateAntipode_universal :
    coefficientRelatedTripleBaseChange
        relatedTripleCoordinateAntipode.toRingHom
        universalCoefficientRelatedTriple =
      universalCoefficientRelatedTriple⁻¹ := by
  exact relatedTripleCoordinateEvaluation_universal _

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
