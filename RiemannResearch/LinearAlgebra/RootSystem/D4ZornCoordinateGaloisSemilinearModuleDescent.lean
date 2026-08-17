/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.GaloisCohomology.GaloisSemilinearModuleDescent
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateSemilinearDescent

/-!
# Galois semilinear module coordinates for D4 related triples

For a finite Galois extension `L/K`, the diagram-twisted action on the
scalar-extended integral related-triple coordinate ring is a semilinear module
action.  The general semilinear Galois tensor decomposition therefore gives an
`L`-linear coordinate equivalence

    L ⊗[K] (L ⊗[ℤ] RelatedTripleCoordinateRing)
      ≃ ((L ≃ₐ[K] L) → (L ⊗[ℤ] RelatedTripleCoordinateRing)).

Its pure-tensor formula is the original D4 coefficient-and-diagram action.

Source: user-provided D4 semilinear-triality descent program.  This module
specializes the general Galois semilinear module tensor equivalence to the
coordinate action constructed in `D4ZornCoordinateSemilinearDescent`.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

noncomputable section

open RiemannResearch.GaloisCohomology

universe u

private abbrev AGalois := RelatedTripleCoordinateRing.{0}

local instance coordinateGaloisSemilinearCommRing : CommRing AGalois :=
  inferInstance

/-- The diagram-twisted D4 coordinate action, packaged as a semilinear action
of the Galois group on the scalar-extended coordinate module. -/
def relatedTripleCoordinateGaloisSemilinearModuleAction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    GaloisSemilinearModuleAction K L
      (RelatedTripleCoordinateScalarExtension L) where
  action γ :=
    (relatedTripleCoordinateSemilinearAction K L diagram γ).toAddEquiv.toAddMonoidHom
  one_act := by
    ext b
    exact congrArg (fun e : AlgEquiv K
      (RelatedTripleCoordinateScalarExtension L)
      (RelatedTripleCoordinateScalarExtension L) => e b)
      (relatedTripleCoordinateSemilinearAction K L diagram).map_one
  mul_act γ δ := by
    ext b
    exact congrArg (fun e : AlgEquiv K
      (RelatedTripleCoordinateScalarExtension L)
      (RelatedTripleCoordinateScalarExtension L) => e b)
      ((relatedTripleCoordinateSemilinearAction K L diagram).map_mul γ δ)
  semilinear γ l b :=
    relatedTripleCoordinateSemilinearAction_smul K L diagram γ l b

/-- The packaged semilinear action has the original D4 coordinate action as
its underlying additive map. -/
@[simp] theorem relatedTripleCoordinateGaloisSemilinearModuleAction_apply
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (γ : L ≃ₐ[K] L) (b : RelatedTripleCoordinateScalarExtension L) :
    (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram).action γ b =
      relatedTripleCoordinateSemilinearAction K L diagram γ b :=
  rfl

/-- Finite-Galois coordinates for the D4 related-triple coordinate module. -/
noncomputable def relatedTripleCoordinateGaloisTensorEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    TensorProduct K L (RelatedTripleCoordinateScalarExtension L) ≃ₗ[L]
      ((L ≃ₐ[K] L) → RelatedTripleCoordinateScalarExtension L) :=
  galoisSemilinearTensorEquiv K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram)

/-- On a pure tensor, the D4 Galois coordinate equivalence applies the
diagram-twisted semilinear action in the module factor. -/
@[simp] theorem relatedTripleCoordinateGaloisTensorEquiv_tmul_apply
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (x : L) (b : RelatedTripleCoordinateScalarExtension L)
    (γ : L ≃ₐ[K] L) :
    relatedTripleCoordinateGaloisTensorEquiv K L diagram
        (x ⊗ₜ[K] b) γ =
      x • relatedTripleCoordinateSemilinearAction K L diagram γ b := by
  exact galoisSemilinearTensorEquiv_tmul_apply K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram)
    x b γ

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
