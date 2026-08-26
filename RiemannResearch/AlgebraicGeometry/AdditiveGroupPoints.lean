/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AdditiveGroupScheme

/-!
# Points of the additive affine group

This file records the coordinate-ring identification of `S`-valued points of
the additive affine line with elements of `S`. It is the point-level bridge
needed later when a genuine E8 root quotient is identified with `Gₐ`.
-/

namespace RiemannResearch
namespace AlgebraicGeometry
namespace AdditiveGroup

universe u v

variable (R : Type u) [CommRing R]

/-- An `R`-algebra morphism from the coordinate ring of `Gₐ` is determined
uniquely by the image of the polynomial generator. -/
noncomputable def pointAlgHomEquiv
    (S : Type v) [CommRing S] [Algebra R S] :
    (Coordinate R →ₐ[R] S) ≃ S where
  toFun f := f Polynomial.X
  invFun s := Polynomial.aeval s
  left_inv f := by
    apply Polynomial.algHom_ext
    simp
  right_inv s := by
    simp

end AdditiveGroup
end AlgebraicGeometry
end RiemannResearch
