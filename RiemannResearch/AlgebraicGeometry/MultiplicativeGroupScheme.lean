/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import RiemannResearch.AlgebraicGeometry.AffineGroupSchemeBaseChange

/-!
# The multiplicative affine group scheme

This file exposes Mathlib's Hopf algebra structure on the Laurent polynomial
ring as the coordinate Hopf algebra of `Gₘ`. The generator `T` is group-like:

`Δ(T) = T ⊗ T`, `ε(T) = 1`, and `S(T) = T⁻¹`.

It also packages evaluation at a unit as an algebra morphism and constructs
the represented affine group scheme. This is the torus building block needed
for integral rank-one coroot morphisms.
-/

open CategoryTheory
open scoped TensorProduct

namespace RiemannResearch
namespace AlgebraicGeometry
namespace MultiplicativeGroup

universe u v

noncomputable section

variable (R : Type u) [CommRing R]

/-- Coordinate ring of the multiplicative group. -/
abbrev Coordinate := LaurentPolynomial R

/-- The Laurent polynomial coordinate ring with its standard Hopf structure. -/
@[instance_reducible] noncomputable def hopfAlgebra :
    HopfAlgebra R (Coordinate R) :=
  LaurentPolynomial.instHopfAlgebra R R

/-- The universal invertible Laurent monomial `T`. -/
noncomputable def generatorUnit : (Coordinate R)ˣ :=
  (LaurentPolynomial.isUnit_T (R := R) (1 : ℤ)).unit

@[simp] theorem coe_generatorUnit :
    ↑(generatorUnit R) = (LaurentPolynomial.T 1 : Coordinate R) := by
  exact IsUnit.unit_spec
    (LaurentPolynomial.isUnit_T (R := R) (1 : ℤ))

/-- Evaluation of Laurent polynomials at a unit, as an algebra morphism. -/
noncomputable def evalAlgHom
    {S : Type v} [CommRing S] [Algebra R S] (u : Sˣ) :
    Coordinate R →ₐ[R] S where
  toRingHom := LaurentPolynomial.eval₂ (algebraMap R S) u
  commutes' r := by simp

@[simp] theorem evalAlgHom_C
    {S : Type v} [CommRing S] [Algebra R S] (u : Sˣ) (r : R) :
    evalAlgHom R u (LaurentPolynomial.C r) = algebraMap R S r := by
  simp [evalAlgHom]

@[simp] theorem evalAlgHom_T
    {S : Type v} [CommRing S] [Algebra R S] (u : Sˣ) (n : ℤ) :
    evalAlgHom R u (LaurentPolynomial.T n) = (u ^ n : Sˣ) := by
  simp [evalAlgHom]

noncomputable local instance coordinateHopf :
    HopfAlgebra R (Coordinate R) :=
  hopfAlgebra R

/-- The Laurent generator is group-like. -/
theorem comul_T :
    CoalgebraStruct.comul (R := R)
        (LaurentPolynomial.T (1 : ℤ) : Coordinate R) =
      (LaurentPolynomial.T 1 : Coordinate R) ⊗ₜ[R]
        (LaurentPolynomial.T 1 : Coordinate R) := by
  change CoalgebraStruct.comul (R := R)
      (AddMonoidAlgebra.single (1 : ℤ) (1 : R)) = _
  rw [AddMonoidAlgebra.comul_single]
  simp [TensorProduct.map_tmul]

/-- The counit sends the Laurent generator to one. -/
theorem counit_T :
    CoalgebraStruct.counit (R := R)
        (LaurentPolynomial.T (1 : ℤ) : Coordinate R) = 1 := by
  change CoalgebraStruct.counit (R := R)
      (AddMonoidAlgebra.single (1 : ℤ) (1 : R)) = 1
  rw [AddMonoidAlgebra.counit_single]
  simp

/-- The antipode inverts the Laurent generator. -/
theorem antipode_T :
    HopfAlgebraStruct.antipode R
        (LaurentPolynomial.T (1 : ℤ) : Coordinate R) =
      (LaurentPolynomial.T (-1) : Coordinate R) := by
  change HopfAlgebraStruct.antipode R
      (AddMonoidAlgebra.single (1 : ℤ) (1 : R)) = _
  rw [AddMonoidAlgebra.antipode_single]
  simp

/-- The multiplicative affine group scheme over `R`. -/
noncomputable def schemeObject :
    Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)) := by
  letI : HopfAlgebra R (Coordinate R) := hopfAlgebra R
  exact affineGroupSchemeObject (CommRingCat.of R)
    (CommRingCat.of (Coordinate R))

set_option linter.style.haveILetI false in
/-- The multiplicative affine scheme carries its expected group-object structure. -/
theorem schemeObject_hasGroupObject : Nonempty (GrpObj (schemeObject R)) := by
  letI : HopfAlgebra R (Coordinate R) := hopfAlgebra R
  simpa [schemeObject] using
    (affineGroupSchemeObject_hasGroupObject (CommRingCat.of R)
      (CommRingCat.of (Coordinate R)))

end

end MultiplicativeGroup
end AlgebraicGeometry
end RiemannResearch
