/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.GaloisCohomology.GaloisSemilinearAlgebraComonadicDescent
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateGaloisSemilinearAlgebraDescent

/-!
# Comonadic algebra structure maps for D4 related triples

This module specializes the generic finite-Galois algebra compatibility to the
coefficient-and-diagram action on the D4 related-triple coordinate algebra.
The coordinate-algebra unit and multiplication are now morphisms of the
existing extension--restriction coalgebras.

No descended algebra, Hopf algebra, affine group scheme, torsor classifier, or
Serre II conclusion is asserted here.

Source: user-provided D4 semilinear-triality descent program.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

noncomputable section

open RiemannResearch.GaloisCohomology

universe u

private abbrev AComonadic := RelatedTripleCoordinateRing.{0}

local instance coordinateGaloisSemilinearComonadicCommRing :
    CommRing AComonadic :=
  inferInstance

/-- The D4 coordinate-algebra unit as a morphism of the finite-Galois
extension--restriction coalgebras. -/
noncomputable def relatedTripleCoordinateGaloisSemilinearUnitDescentMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :=
  galoisSemilinearAlgebraUnitDescentMap K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram)

/-- D4 coordinate-algebra multiplication as a morphism of the finite-Galois
extension--restriction coalgebras. -/
noncomputable def relatedTripleCoordinateGaloisSemilinearMulDescentMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :=
  galoisSemilinearAlgebraMulDescentMap K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram)

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
