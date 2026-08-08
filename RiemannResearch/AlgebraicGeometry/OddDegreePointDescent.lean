/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.PointFields

/-!
# Odd-degree point descent

An abstract implication pattern used in the E8 case of Serre II: odd-degree
splitting, a point-neutrality equivalence, and descent of points along the
chosen odd-degree extensions imply neutrality over the base.

The motivating statement is completion target A in the 5 August 2026 E8
Serre II memorandum. This module isolates only its general point-descent logic.
-/

namespace RiemannResearch.AlgebraicGeometry

/-- If every candidate class is neutral over some odd-degree extension, points
are equivalent to neutrality over every extension, and points descend along
those odd-degree extensions, then every candidate is neutral over the base.

In the E8 application, the point predicate may be instantiated by the Borel
variety, the EVIII variety, or the corrected one-sided wonderful
compactification. -/
theorem neutral_of_oddDegreePointDescent
    {Class Extension : Type*}
    (base : Extension)
    (OddDegree : Extension → Prop)
    (hasPoint neutral : Class → Extension → Prop)
    (oddSplitting : ∀ ξ, ∃ L, OddDegree L ∧ neutral ξ L)
    (point_iff_neutral : ∀ ξ L, hasPoint ξ L ↔ neutral ξ L)
    (oddPointDescent :
      ∀ ξ L, OddDegree L → hasPoint ξ L → hasPoint ξ base) :
    ∀ ξ, neutral ξ base := by
  intro ξ
  obtain ⟨L, hOdd, hNeutral⟩ := oddSplitting ξ
  apply (point_iff_neutral ξ base).mp
  exact oddPointDescent ξ L hOdd
    ((point_iff_neutral ξ L).mpr hNeutral)

end RiemannResearch.AlgebraicGeometry
