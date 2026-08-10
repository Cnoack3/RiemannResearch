/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AffineGroupSchemeBaseChange
import RiemannResearch.AlgebraicGeometry.FpqcH1

/-!
# Scalar-extension interface for fpqc H¹

This module fixes the concrete source and target of restriction along a finite
field extension. If an affine group over `K` has coordinate Hopf algebra
`A`, its scalar extension to `L` has coordinate algebra `L ⊗[K] A`.

The structure `FpqcH1ScalarExtensionMap` is intentionally an interface: it
does not claim that the global Cech quotient in `FpqcH1` has already been
made functorial under scalar extension. Constructing `toFun`, proving its
composition laws, and comparing it with torsor pullback remain open.
-/

namespace RiemannResearch.AlgebraicGeometry

universe u

noncomputable section

/-- A field extension bundled with the finiteness needed for its degree. -/
structure FiniteFieldExtension (K : Type u) [Field K] where
  Extension : Type u
  field : Field Extension
  algebra : Algebra K Extension
  finiteDimensional : FiniteDimensional K Extension

namespace FiniteFieldExtension

variable {K : Type u} [Field K]

instance (E : FiniteFieldExtension K) : Field E.Extension := E.field
instance (E : FiniteFieldExtension K) : Algebra K E.Extension := E.algebra
instance (E : FiniteFieldExtension K) : FiniteDimensional K E.Extension :=
  E.finiteDimensional

/-- The vector-space degree of a bundled finite field extension. -/
def degree (E : FiniteFieldExtension K) : ℕ :=
  Module.finrank K E.Extension

end FiniteFieldExtension

/-- Fpqc H¹ of the actual tensor-product base change of an affine group. -/
abbrev baseChangedFpqcH1
    (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A]
    (E : FiniteFieldExtension K) :=
  FpqcH1
    (CommRingCat.of E.Extension)
    (CommRingCat.of (affineGroupBaseChangeCoordinate K E.Extension A))

/-- A proposed scalar-extension map on global fpqc H¹, with its pointed law.

The target is not an arbitrary local pointed set: it is fpqc H¹ of the
tensor-product base-changed Hopf algebra. -/
structure FpqcH1ScalarExtensionMap
    (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A]
    (E : FiniteFieldExtension K) where
  toFun :
    FpqcH1 (CommRingCat.of K) (CommRingCat.of A) →
      baseChangedFpqcH1 K A E
  map_neutral :
    toFun (FpqcH1.neutral (CommRingCat.of K) (CommRingCat.of A)) =
      FpqcH1.neutral
        (CommRingCat.of E.Extension)
        (CommRingCat.of (affineGroupBaseChangeCoordinate K E.Extension A))

/-- A family of finite extensions equipped with concrete fpqc-H¹ restriction
maps to the corresponding tensor-product base changes. -/
structure FpqcH1RestrictionSystem
    (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A] where
  Index : Type (u + 1)
  extension : Index → FiniteFieldExtension K
  map : ∀ i, FpqcH1ScalarExtensionMap K A (extension i)

namespace FpqcH1RestrictionSystem

variable {K A : Type u} [Field K] [CommRing A] [HopfAlgebra K A]

/-- Degree of a member of a concrete fpqc-H¹ restriction system. -/
def degree (D : FpqcH1RestrictionSystem K A) (i : D.Index) : ℕ :=
  (D.extension i).degree

@[simp] theorem map_neutral
    (D : FpqcH1RestrictionSystem K A) (i : D.Index) :
    (D.map i).toFun
        (FpqcH1.neutral (CommRingCat.of K) (CommRingCat.of A)) =
      FpqcH1.neutral
        (CommRingCat.of (D.extension i).Extension)
        (CommRingCat.of
          (affineGroupBaseChangeCoordinate
            K (D.extension i).Extension A)) :=
  (D.map i).map_neutral

end FpqcH1RestrictionSystem

end

end RiemannResearch.AlgebraicGeometry
