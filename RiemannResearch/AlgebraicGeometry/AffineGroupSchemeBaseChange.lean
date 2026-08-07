import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Affine group schemes from Hopf algebras

This file records the scheme-level construction already supplied by Mathlib:
a commutative Hopf algebra over a commutative base ring represents an affine
group object over the spectrum of the base.  It also packages the tensor
product Hopf algebra used for scalar extension.

These declarations construct genuine affine group objects.  They do not by
themselves assert finite presentation, smoothness, reductivity, or a root
datum for the represented group scheme.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

universe u

noncomputable section

/-- The affine scheme over `Spec R` represented by a commutative
`R`-Hopf algebra `A`.  Mathlib equips this object with a group-object
instance. -/
abbrev affineGroupSchemeObject
    (R A : CommRingCat.{u}) [HopfAlgebra R A] :
    Over (_root_.AlgebraicGeometry.Spec R) :=
  (_root_.AlgebraicGeometry.Spec A).asOver
    (_root_.AlgebraicGeometry.Spec R)

/-- A commutative Hopf algebra represents a genuine affine group object over
the spectrum of its base ring. -/
theorem affineGroupSchemeObject_hasGroupObject
    (R A : CommRingCat.{u}) [HopfAlgebra R A] :
    Nonempty (GrpObj (affineGroupSchemeObject R A)) :=
  ⟨inferInstance⟩

/-- Coordinate ring for scalar extension of a commutative Hopf algebra from
`R` to an `R`-algebra `S`. -/
abbrev affineGroupBaseChangeCoordinate
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :=
  TensorProduct R S A

/-- Tensor-product scalar extension carries the Hopf-algebra structure needed
to represent the base-changed affine group scheme. -/
theorem affineGroupBaseChangeCoordinate_hasHopfAlgebra
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    Nonempty (HopfAlgebra S (affineGroupBaseChangeCoordinate R S A)) :=
  ⟨inferInstance⟩

/-- The affine scheme represented by the tensor-product coordinate algebra
after extending scalars from `R` to `S`. -/
abbrev affineGroupBaseChangeSchemeObject
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of S)) :=
  affineGroupSchemeObject (CommRingCat.of S)
    (CommRingCat.of (affineGroupBaseChangeCoordinate R S A))

/-- The tensor-product scalar extension is again a genuine affine group object
over the spectrum of the extended base ring. -/
theorem affineGroupBaseChangeSchemeObject_hasGroupObject
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    Nonempty (GrpObj (affineGroupBaseChangeSchemeObject R S A)) :=
  ⟨inferInstance⟩

end

end RiemannResearch.AlgebraicGeometry
