/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import RiemannResearch.AlgebraicGeometry.AffineGroupSchemeBaseChange

/-!
# The additive affine group scheme

This file constructs the coordinate Hopf algebra of the additive group directly
on `Polynomial R`.  The generator is primitive:

`Δ(X) = X ⊗ 1 + 1 ⊗ X`, `ε(X) = 0`, and `S(X) = -X`.

The construction is deliberately independent of the E8 development.  It is the
concrete `Gₐ` building block needed before an E8 root-subgroup morphism can be
formalized.  This file does not claim to construct any Chevalley group or root
subgroup inside E8.
-/

open scoped TensorProduct
open CategoryTheory

namespace RiemannResearch.AlgebraicGeometry.AdditiveGroup

universe u

variable (R : Type u) [CommRing R]

/-- Coordinate ring of the additive group. -/
abbrev Coordinate := Polynomial R

/-- Additive comultiplication, determined by the primitive generator `X`. -/
noncomputable def comul :
    Coordinate R →ₐ[R] TensorProduct R (Coordinate R) (Coordinate R) :=
  Polynomial.aeval
    ((Algebra.TensorProduct.includeLeft (R := R) (S := R)
      (A := Coordinate R) (B := Coordinate R)) Polynomial.X +
    (Algebra.TensorProduct.includeRight (R := R)
      (A := Coordinate R) (B := Coordinate R)) Polynomial.X)

/-- Additive counit, evaluation at zero. -/
noncomputable def counit : Coordinate R →ₐ[R] R :=
  Polynomial.aeval 0

/-- Additive antipode, substitution `X ↦ -X`. -/
noncomputable def antipode : Coordinate R →ₐ[R] Coordinate R :=
  Polynomial.aeval (-Polynomial.X)

/-- The polynomial coordinate ring with its additive bialgebra structure. -/
@[instance_reducible] noncomputable def bialgebra :
    Bialgebra R (Coordinate R) :=
  Bialgebra.ofAlgHom (comul R) (counit R)
    (by
      apply Polynomial.algHom_ext
      simp [comul, Algebra.TensorProduct.includeLeft,
        Algebra.TensorProduct.includeRight,
        Algebra.TensorProduct.assoc_tmul, TensorProduct.add_tmul,
        TensorProduct.tmul_add, Algebra.TensorProduct.one_def, add_assoc])
    (by
      apply Polynomial.algHom_ext
      simp [comul, counit, Algebra.TensorProduct.includeLeft,
        Algebra.TensorProduct.includeRight])
    (by
      apply Polynomial.algHom_ext
      simp [comul, counit, Algebra.TensorProduct.includeLeft,
        Algebra.TensorProduct.includeRight])

/-- The polynomial coordinate ring with the Hopf structure representing
the additive group `Gₐ`. -/
@[instance_reducible] noncomputable def hopfAlgebra :
    HopfAlgebra R (Coordinate R) := by
  letI : Bialgebra R (Coordinate R) := bialgebra R
  have hx : CoalgebraStruct.comul (R := R) (A := Coordinate R)
      (Polynomial.X : Coordinate R) =
      Polynomial.X ⊗ₜ[R] (1 : Coordinate R) +
        (1 : Coordinate R) ⊗ₜ[R] Polynomial.X := by
    change (comul R).toLinearMap (Polynomial.X : Coordinate R) = _
    simp [comul, Algebra.TensorProduct.includeLeft,
      Algebra.TensorProduct.includeRight]
  have he : CoalgebraStruct.counit (R := R) (A := Coordinate R)
      (Polynomial.X : Coordinate R) = (0 : R) := by
    change (counit R).toLinearMap (Polynomial.X : Coordinate R) = 0
    simp [counit]
  apply HopfAlgebra.ofAlgHom (antipode R)
  · apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    change (Algebra.TensorProduct.lift (antipode R)
        (AlgHom.id R (Coordinate R)) _)
        (CoalgebraStruct.comul (Polynomial.X : Coordinate R)) =
      (Algebra.ofId R (Coordinate R))
        (CoalgebraStruct.counit (Polynomial.X : Coordinate R))
    rw [hx, he]
    simp [antipode]
  · apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    change (Algebra.TensorProduct.lift (AlgHom.id R (Coordinate R))
        (antipode R) _)
        (CoalgebraStruct.comul (Polynomial.X : Coordinate R)) =
      (Algebra.ofId R (Coordinate R))
        (CoalgebraStruct.counit (Polynomial.X : Coordinate R))
    rw [hx, he]
    simp [antipode]

/-- The additive affine group scheme over `R`. -/
noncomputable def schemeObject :
    Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)) := by
  letI : HopfAlgebra R (Coordinate R) := hopfAlgebra R
  exact affineGroupSchemeObject (CommRingCat.of R)
    (CommRingCat.of (Coordinate R))

set_option linter.style.haveILetI false in
/-- The additive affine scheme carries the expected group-object structure. -/
theorem schemeObject_hasGroupObject : Nonempty (GrpObj (schemeObject R)) := by
  letI : HopfAlgebra R (Coordinate R) := hopfAlgebra R
  simpa [schemeObject] using
    (affineGroupSchemeObject_hasGroupObject (CommRingCat.of R)
      (CommRingCat.of (Coordinate R)))

end AdditiveGroup
end AlgebraicGeometry
end RiemannResearch
