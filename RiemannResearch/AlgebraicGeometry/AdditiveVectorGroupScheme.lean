/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.MvPolynomial.Basic
import RiemannResearch.AlgebraicGeometry.AffineGroupSchemeBaseChange

/-!
# Additive vector groups

For a commutative ring `R` and an index type `ι` in the same universe, this
file constructs the coordinate Hopf algebra

`R[X_i | i : ι]`

of the additive vector group.  Every coordinate is primitive:

* `Δ(X_i) = X_i ⊗ 1 + 1 ⊗ X_i`;
* `ε(X_i) = 0`;
* `S(X_i) = -X_i`.

The construction is reusable for the vector-group quotients in root-height
filtrations.  In particular, `ι = Fin 2` gives the quotient `Gₐ²` occurring
in the central extension of the three-dimensional upper-unitriangular group.
-/

open CategoryTheory
open scoped TensorProduct

namespace RiemannResearch
namespace AlgebraicGeometry
namespace AdditiveVectorGroup

universe u

variable (R : Type u) [CommRing R]
variable (ι : Type u)

/-- Coordinate algebra of the additive vector group indexed by `ι`. -/
abbrev Coordinate := MvPolynomial ι R

private abbrev TensorCoordinate :=
  TensorProduct R (Coordinate R ι) (Coordinate R ι)

private noncomputable def includeLeft :
    Coordinate R ι →ₐ[R] TensorCoordinate R ι :=
  Algebra.TensorProduct.includeLeft

private noncomputable def includeRight :
    Coordinate R ι →ₐ[R] TensorCoordinate R ι :=
  Algebra.TensorProduct.includeRight

/-- Comultiplication with every coordinate primitive. -/
noncomputable def comul :
    Coordinate R ι →ₐ[R] TensorCoordinate R ι :=
  MvPolynomial.aeval (fun i : ι =>
    includeLeft R ι (MvPolynomial.X i) +
      includeRight R ι (MvPolynomial.X i))

/-- Counit given by evaluation at the zero vector. -/
noncomputable def counit : Coordinate R ι →ₐ[R] R :=
  MvPolynomial.aeval (fun _ : ι => (0 : R))

/-- Antipode given by coordinatewise negation. -/
noncomputable def antipode :
    Coordinate R ι →ₐ[R] Coordinate R ι :=
  MvPolynomial.aeval
    (fun i : ι => -(MvPolynomial.X i : Coordinate R ι))

@[simp] theorem comul_X (i : ι) :
    comul R ι (MvPolynomial.X i) =
      MvPolynomial.X i ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] MvPolynomial.X i := by
  simp [comul, includeLeft, includeRight]

@[simp] theorem counit_X (i : ι) :
    counit R ι (MvPolynomial.X i) = 0 := by
  simp [counit]

@[simp] theorem antipode_X (i : ι) :
    antipode R ι (MvPolynomial.X i) =
      -MvPolynomial.X i := by
  simp [antipode]

private theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R
      (Coordinate R ι) (Coordinate R ι) (Coordinate R ι)).toAlgHom.comp
        ((Algebra.TensorProduct.map (comul R ι)
          (AlgHom.id R (Coordinate R ι))).comp (comul R ι)) =
      (Algebra.TensorProduct.map (AlgHom.id R (Coordinate R ι))
        (comul R ι)).comp (comul R ι) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.one_def,
    TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

private theorem comul_rTensor_counit :
    (Algebra.TensorProduct.map (counit R ι)
      (AlgHom.id R (Coordinate R ι))).comp (comul R ι) =
      (Algebra.TensorProduct.lid R (Coordinate R ι)).symm.toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [comul, counit, includeLeft, includeRight]

private theorem comul_lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id R (Coordinate R ι))
      (counit R ι)).comp (comul R ι) =
      (Algebra.TensorProduct.rid R R (Coordinate R ι)).symm.toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [comul, counit, includeLeft, includeRight]

/-- The polynomial coordinate algebra with its vector-group bialgebra
structure. -/
@[instance_reducible] noncomputable def bialgebra :
    Bialgebra R (Coordinate R ι) :=
  Bialgebra.ofAlgHom (comul R ι) (counit R ι)
    (comul_coassoc R ι)
    (comul_rTensor_counit R ι)
    (comul_lTensor_counit R ι)

/-- The polynomial coordinate algebra with the Hopf structure representing
the additive vector group. -/
@[instance_reducible] noncomputable def hopfAlgebra :
    HopfAlgebra R (Coordinate R ι) := by
  letI : Bialgebra R (Coordinate R ι) := bialgebra R ι
  have hx (i : ι) :
      CoalgebraStruct.comul (R := R) (A := Coordinate R ι)
        (MvPolynomial.X i) =
      MvPolynomial.X i ⊗ₜ[R] (1 : Coordinate R ι) +
        (1 : Coordinate R ι) ⊗ₜ[R] MvPolynomial.X i := by
    change (comul R ι).toLinearMap (MvPolynomial.X i) = _
    exact comul_X R ι i
  have he (i : ι) :
      CoalgebraStruct.counit (R := R) (A := Coordinate R ι)
        (MvPolynomial.X i) = (0 : R) := by
    change (counit R ι).toLinearMap (MvPolynomial.X i) = 0
    exact counit_X R ι i
  apply HopfAlgebra.ofAlgHom (antipode R ι)
  · apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    change (Algebra.TensorProduct.lift (antipode R ι)
        (AlgHom.id R (Coordinate R ι)) _)
        (CoalgebraStruct.comul (R := R) (A := Coordinate R ι)
          (MvPolynomial.X i)) =
      (Algebra.ofId R (Coordinate R ι))
        (CoalgebraStruct.counit (R := R) (A := Coordinate R ι)
          (MvPolynomial.X i))
    rw [hx i, he i]
    simp [antipode]
  · apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    change (Algebra.TensorProduct.lift (AlgHom.id R (Coordinate R ι))
        (antipode R ι) _)
        (CoalgebraStruct.comul (R := R) (A := Coordinate R ι)
          (MvPolynomial.X i)) =
      (Algebra.ofId R (Coordinate R ι))
        (CoalgebraStruct.counit (R := R) (A := Coordinate R ι)
          (MvPolynomial.X i))
    rw [hx i, he i]
    simp [antipode]

/-- The additive vector-group affine scheme over `R`. -/
noncomputable def schemeObject :
    Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)) := by
  letI : HopfAlgebra R (Coordinate R ι) := hopfAlgebra R ι
  exact affineGroupSchemeObject (CommRingCat.of R)
    (CommRingCat.of (Coordinate R ι))

set_option linter.style.haveILetI false in
/-- The represented affine scheme carries its canonical group-object
structure. -/
theorem schemeObject_hasGroupObject :
    Nonempty (GrpObj (schemeObject R ι)) := by
  letI : HopfAlgebra R (Coordinate R ι) := hopfAlgebra R ι
  simpa [schemeObject] using
    (affineGroupSchemeObject_hasGroupObject (CommRingCat.of R)
      (CommRingCat.of (Coordinate R ι)))

end AdditiveVectorGroup
end AlgebraicGeometry
end RiemannResearch
