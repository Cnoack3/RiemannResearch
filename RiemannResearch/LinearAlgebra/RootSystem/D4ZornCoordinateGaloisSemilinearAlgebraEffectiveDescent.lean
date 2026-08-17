/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.GaloisCohomology.GaloisSemilinearAlgebraEffectiveDescent
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateGaloisSemilinearAlgebraDescent

/-!
# Effective algebra-map descent for D4 related triples

This module specializes the inverse-comonadic transport of algebra structure
maps and the scalar-extension tensor comparison to the coefficient-and-diagram
action on the D4 related-triple coordinate algebra.

The tensor comparison has only been constructed after scalar extension. No
descended coordinate algebra, Hopf algebra, affine group scheme, or Serre II
conclusion is asserted.

Source: user-provided D4 semilinear-triality descent program.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

noncomputable section

open RiemannResearch.GaloisCohomology

universe u

private abbrev AEffective := RelatedTripleCoordinateRing.{0}

local instance coordinateGaloisSemilinearEffectiveCommRing :
    CommRing AEffective :=
  inferInstance

noncomputable def relatedTripleCoordinateGaloisSemilinearUnitDescendedMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :=
  galoisSemilinearAlgebraUnitDescendedMap K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram)

noncomputable def relatedTripleCoordinateGaloisSemilinearMulDescendedMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :=
  galoisSemilinearAlgebraMulDescendedMap K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram)

noncomputable def relatedTripleCoordinateGaloisSemilinearTensorComparisonBaseChangeIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :=
  galoisSemilinearDescendedTensorComparisonBaseChangeIso K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram)

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
