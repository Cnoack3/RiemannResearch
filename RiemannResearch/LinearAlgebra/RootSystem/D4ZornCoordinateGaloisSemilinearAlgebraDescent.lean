/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.GaloisCohomology.GaloisSemilinearAlgebraCoaction
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateGaloisSemilinearModuleDescent

/-!
# Galois semilinear algebra coordinates for D4 related triples

The coefficient-and-diagram action on the scalar-extended D4 related-triple
coordinate ring already acts by algebra automorphisms.  This module packages
that action as a Galois semilinear algebra action and specializes the generic
algebra-valued tensor coordinates.  It thereby upgrades the existing
finite-Galois linear equivalence to an algebra equivalence and packages the
existing module coaction as an algebra homomorphism.

No effective algebra descent, Hopf descent, affine group scheme, or Serre II
conclusion is asserted here.

Source: user-provided D4 semilinear-triality descent program.  The construction
reuses the algebra action from D4ZornCoordinateSemilinearDescent and the module
coordinates from D4ZornCoordinateGaloisSemilinearModuleDescent.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

noncomputable section

open RiemannResearch.GaloisCohomology

universe u

private abbrev AGaloisAlgebra := RelatedTripleCoordinateRing.{0}

local instance coordinateGaloisSemilinearAlgebraCommRing :
    CommRing AGaloisAlgebra :=
  inferInstance

/-- The additive D4 Galois action retains the unit law of the underlying
algebra action. -/
@[simp] theorem relatedTripleCoordinateGaloisSemilinearModuleAction_one
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (γ : L ≃ₐ[K] L) :
    (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram).action γ
        (1 : RelatedTripleCoordinateScalarExtension L) = 1 := by
  rw [relatedTripleCoordinateGaloisSemilinearModuleAction_apply]
  exact (relatedTripleCoordinateSemilinearAction K L diagram γ).map_one

/-- The additive D4 Galois action retains the multiplication law of the
underlying algebra action. -/
theorem relatedTripleCoordinateGaloisSemilinearModuleAction_mul
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (γ : L ≃ₐ[K] L) (x y : RelatedTripleCoordinateScalarExtension L) :
    (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram).action γ
        (x * y) =
      (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram).action γ x *
        (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram).action γ y := by
  rw [relatedTripleCoordinateGaloisSemilinearModuleAction_apply,
    relatedTripleCoordinateGaloisSemilinearModuleAction_apply]
  exact (relatedTripleCoordinateSemilinearAction K L diagram γ).map_mul x y

/-- The coefficient-and-diagram D4 action as a semilinear algebra action. -/
def relatedTripleCoordinateGaloisSemilinearAlgebraAction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    GaloisSemilinearAlgebraAction K L
      (RelatedTripleCoordinateScalarExtension L) where
  action := relatedTripleCoordinateSemilinearAction K L diagram
  semilinear := relatedTripleCoordinateSemilinearAction_smul K L diagram

/-- Forgetting the D4 semilinear algebra structure gives exactly the existing
semilinear module action. -/
@[simp] theorem relatedTripleCoordinateGaloisSemilinearAlgebraAction_toModuleAction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram).toModuleAction
        K L (RelatedTripleCoordinateScalarExtension L) =
      relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram := by
  rfl

/-- Finite-Galois algebra coordinates for the D4 related-triple coordinate
algebra. -/
noncomputable def relatedTripleCoordinateGaloisTensorAlgEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    TensorProduct K L (RelatedTripleCoordinateScalarExtension L) ≃ₐ[L]
      ((L ≃ₐ[K] L) → RelatedTripleCoordinateScalarExtension L) :=
  galoisSemilinearTensorAlgEquiv K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram)

/-- The D4 algebra coordinate equivalence is exactly the previously verified
linear coordinate equivalence after forgetting multiplication. -/
@[simp] theorem relatedTripleCoordinateGaloisTensorAlgEquiv_toLinearEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    (relatedTripleCoordinateGaloisTensorAlgEquiv K L diagram).toLinearEquiv =
      relatedTripleCoordinateGaloisTensorEquiv K L diagram := by
  rfl

/-- The D4 finite-Galois coaction as an L-algebra homomorphism. -/
noncomputable def relatedTripleCoordinateGaloisSemilinearCoactionAlgHom
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    RelatedTripleCoordinateScalarExtension L →ₐ[L]
      TensorProduct K L (RelatedTripleCoordinateScalarExtension L) :=
  galoisSemilinearAlgebraCoaction K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram)

/-- Forgetting multiplication in the D4 algebra coaction gives exactly the
previously constructed module coaction. -/
theorem relatedTripleCoordinateGaloisSemilinearCoactionAlgHom_toLinearMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    (relatedTripleCoordinateGaloisSemilinearCoactionAlgHom K L diagram).toLinearMap =
      galoisSemilinearCoaction K L
        (RelatedTripleCoordinateScalarExtension L)
        (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram) := by
  rfl

/-- The D4 semilinear module coaction preserves the coordinate-algebra unit. -/
@[simp] theorem relatedTripleCoordinateGaloisSemilinearCoaction_one
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    galoisSemilinearCoaction K L
        (RelatedTripleCoordinateScalarExtension L)
        (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram) 1 = 1 := by
  rw [← relatedTripleCoordinateGaloisSemilinearCoactionAlgHom_toLinearMap
    K L diagram]
  exact (relatedTripleCoordinateGaloisSemilinearCoactionAlgHom K L diagram).map_one

/-- The D4 semilinear module coaction preserves coordinate-algebra
multiplication. -/
theorem relatedTripleCoordinateGaloisSemilinearCoaction_mul
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (x y : RelatedTripleCoordinateScalarExtension L) :
    galoisSemilinearCoaction K L
        (RelatedTripleCoordinateScalarExtension L)
        (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram) (x * y) =
      galoisSemilinearCoaction K L
          (RelatedTripleCoordinateScalarExtension L)
          (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram) x *
        galoisSemilinearCoaction K L
          (RelatedTripleCoordinateScalarExtension L)
          (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram) y := by
  rw [← relatedTripleCoordinateGaloisSemilinearCoactionAlgHom_toLinearMap
    K L diagram]
  exact
    (relatedTripleCoordinateGaloisSemilinearCoactionAlgHom K L diagram).map_mul x y

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
