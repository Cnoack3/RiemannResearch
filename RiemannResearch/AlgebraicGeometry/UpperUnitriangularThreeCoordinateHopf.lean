/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import RiemannResearch.AlgebraicGeometry.AffineGroupSchemeBaseChange
import RiemannResearch.AlgebraicGeometry.UpperUnitriangularThreePoints

/-!
# Coordinate Hopf algebra of the split three-dimensional upper-unitriangular group

This file represents the pointwise Heisenberg group from
`UpperUnitriangularThreePoints` by the polynomial algebra

`ℤ[x₁₂, x₂₃, x₁₃]`.

The structure maps are dual to

`(a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab')`:

* `Δ(x₁₂) = x₁₂ ⊗ 1 + 1 ⊗ x₁₂`;
* `Δ(x₂₃) = x₂₃ ⊗ 1 + 1 ⊗ x₂₃`;
* `Δ(x₁₃) = x₁₃ ⊗ 1 + 1 ⊗ x₁₃ + x₁₂ ⊗ x₂₃`;
* `ε(xᵢⱼ) = 0`;
* `S(x₁₂) = -x₁₂`, `S(x₂₃) = -x₂₃`, and
  `S(x₁₃) = -x₁₃ + x₁₂x₂₃`.

Thus this is the first genuine nonabelian unipotent affine group scheme in the
root-height program. It is a rank-two model only; no E8 group scheme is
claimed here.
-/

open scoped TensorProduct
open CategoryTheory

namespace RiemannResearch
namespace AlgebraicGeometry
namespace UpperUnitriangularThree

noncomputable section

/-- The three ordered positive-root coordinates `(12,23,13)`. -/
abbrev Variable := Fin 3

/-- Integral coordinate algebra of the split upper-unitriangular group `U₃`. -/
abbrev Coordinate := MvPolynomial Variable ℤ

/-- The simple-root coordinate `x₁₂`. -/
abbrev x12 : Coordinate := MvPolynomial.X 0

/-- The simple-root coordinate `x₂₃`. -/
abbrev x23 : Coordinate := MvPolynomial.X 1

/-- The height-two coordinate `x₁₃`. -/
abbrev x13 : Coordinate := MvPolynomial.X 2

private abbrev TensorCoordinate :=
  TensorProduct ℤ Coordinate Coordinate

private noncomputable def includeLeft : Coordinate →ₐ[ℤ] TensorCoordinate :=
  Algebra.TensorProduct.includeLeft

private noncomputable def includeRight : Coordinate →ₐ[ℤ] TensorCoordinate :=
  Algebra.TensorProduct.includeRight

/-- Comultiplication dual to upper-unitriangular matrix multiplication. -/
noncomputable def comul : Coordinate →ₐ[ℤ] TensorCoordinate :=
  MvPolynomial.aeval ![
    includeLeft x12 + includeRight x12,
    includeLeft x23 + includeRight x23,
    includeLeft x13 + includeRight x13 + includeLeft x12 * includeRight x23]

/-- Counit dual to the identity point. -/
noncomputable def counit : Coordinate →ₐ[ℤ] ℤ :=
  MvPolynomial.aeval (fun _ => 0)

/-- Antipode dual to upper-unitriangular inversion. -/
noncomputable def antipode : Coordinate →ₐ[ℤ] Coordinate :=
  MvPolynomial.aeval ![-x12, -x23, -x13 + x12 * x23]

@[simp] theorem comul_x12 :
    comul x12 = x12 ⊗ₜ[ℤ] 1 + 1 ⊗ₜ[ℤ] x12 := by
  simp [comul, x12, includeLeft, includeRight,
    Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]

@[simp] theorem comul_x23 :
    comul x23 = x23 ⊗ₜ[ℤ] 1 + 1 ⊗ₜ[ℤ] x23 := by
  simp [comul, x23, includeLeft, includeRight,
    Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]

@[simp] theorem comul_x13 :
    comul x13 =
      x13 ⊗ₜ[ℤ] 1 + 1 ⊗ₜ[ℤ] x13 + x12 ⊗ₜ[ℤ] x23 := by
  simp [comul, x12, x23, x13, includeLeft, includeRight,
    Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]

@[simp] theorem counit_x12 : counit x12 = 0 := by
  simp [counit, x12]

@[simp] theorem counit_x23 : counit x23 = 0 := by
  simp [counit, x23]

@[simp] theorem counit_x13 : counit x13 = 0 := by
  simp [counit, x13]

@[simp] theorem antipode_x12 : antipode x12 = -x12 := by
  simp [antipode, x12]

@[simp] theorem antipode_x23 : antipode x23 = -x23 := by
  simp [antipode, x23]

@[simp] theorem antipode_x13 : antipode x13 = -x13 + x12 * x23 := by
  simp [antipode, x12, x23, x13]

private theorem comul_coassoc :
    (Algebra.TensorProduct.assoc ℤ ℤ ℤ Coordinate Coordinate Coordinate).toAlgHom.comp
        ((Algebra.TensorProduct.map comul (AlgHom.id ℤ Coordinate)).comp comul) =
      (Algebra.TensorProduct.map (AlgHom.id ℤ Coordinate) comul).comp comul := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.one_def,
      TensorProduct.add_tmul, TensorProduct.tmul_add] <;> abel

private theorem comul_rTensor_counit :
    (Algebra.TensorProduct.lid ℤ ℤ Coordinate).toAlgHom.comp
        ((Algebra.TensorProduct.map counit (AlgHom.id ℤ Coordinate)).comp comul) =
      AlgHom.id ℤ Coordinate := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]

private theorem comul_lTensor_counit :
    (Algebra.TensorProduct.rid ℤ ℤ Coordinate).toAlgHom.comp
        ((Algebra.TensorProduct.map (AlgHom.id ℤ Coordinate) counit).comp comul) =
      AlgHom.id ℤ Coordinate := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]

/-- The polynomial coordinate algebra with its upper-unitriangular bialgebra
structure. -/
@[instance_reducible] noncomputable def bialgebra :
    Bialgebra ℤ Coordinate :=
  Bialgebra.ofAlgHom comul counit comul_coassoc
    comul_rTensor_counit comul_lTensor_counit

/-- The polynomial coordinate algebra with the Hopf structure representing
`U₃`. -/
@[instance_reducible] noncomputable def hopfAlgebra :
    HopfAlgebra ℤ Coordinate := by
  letI : Bialgebra ℤ Coordinate := bialgebra
  have h12 : CoalgebraStruct.comul (R := ℤ) (A := Coordinate) x12 =
      x12 ⊗ₜ[ℤ] (1 : Coordinate) + (1 : Coordinate) ⊗ₜ[ℤ] x12 := by
    change comul.toLinearMap x12 = _
    exact comul_x12
  have h23 : CoalgebraStruct.comul (R := ℤ) (A := Coordinate) x23 =
      x23 ⊗ₜ[ℤ] (1 : Coordinate) + (1 : Coordinate) ⊗ₜ[ℤ] x23 := by
    change comul.toLinearMap x23 = _
    exact comul_x23
  have h13 : CoalgebraStruct.comul (R := ℤ) (A := Coordinate) x13 =
      x13 ⊗ₜ[ℤ] (1 : Coordinate) + (1 : Coordinate) ⊗ₜ[ℤ] x13 +
        x12 ⊗ₜ[ℤ] x23 := by
    change comul.toLinearMap x13 = _
    exact comul_x13
  have e12 : CoalgebraStruct.counit (R := ℤ) (A := Coordinate) x12 = (0 : ℤ) := by
    change counit.toLinearMap x12 = 0
    exact counit_x12
  have e23 : CoalgebraStruct.counit (R := ℤ) (A := Coordinate) x23 = (0 : ℤ) := by
    change counit.toLinearMap x23 = 0
    exact counit_x23
  have e13 : CoalgebraStruct.counit (R := ℤ) (A := Coordinate) x13 = (0 : ℤ) := by
    change counit.toLinearMap x13 = 0
    exact counit_x13
  apply HopfAlgebra.ofAlgHom antipode
  · apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · rw [AlgHom.comp_apply, AlgHom.comp_apply]
      change (Algebra.TensorProduct.lift antipode
          (AlgHom.id ℤ Coordinate) _)
          (CoalgebraStruct.comul x12) =
        (Algebra.ofId ℤ Coordinate) (CoalgebraStruct.counit x12)
      rw [h12, e12]
      simp [antipode]
    · rw [AlgHom.comp_apply, AlgHom.comp_apply]
      change (Algebra.TensorProduct.lift antipode
          (AlgHom.id ℤ Coordinate) _)
          (CoalgebraStruct.comul x23) =
        (Algebra.ofId ℤ Coordinate) (CoalgebraStruct.counit x23)
      rw [h23, e23]
      simp [antipode]
    · rw [AlgHom.comp_apply, AlgHom.comp_apply]
      change (Algebra.TensorProduct.lift antipode
          (AlgHom.id ℤ Coordinate) _)
          (CoalgebraStruct.comul x13) =
        (Algebra.ofId ℤ Coordinate) (CoalgebraStruct.counit x13)
      rw [h13, e13]
      simp [antipode]
      ring
  · apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · rw [AlgHom.comp_apply, AlgHom.comp_apply]
      change (Algebra.TensorProduct.lift (AlgHom.id ℤ Coordinate)
          antipode _)
          (CoalgebraStruct.comul x12) =
        (Algebra.ofId ℤ Coordinate) (CoalgebraStruct.counit x12)
      rw [h12, e12]
      simp [antipode]
    · rw [AlgHom.comp_apply, AlgHom.comp_apply]
      change (Algebra.TensorProduct.lift (AlgHom.id ℤ Coordinate)
          antipode _)
          (CoalgebraStruct.comul x23) =
        (Algebra.ofId ℤ Coordinate) (CoalgebraStruct.counit x23)
      rw [h23, e23]
      simp [antipode]
    · rw [AlgHom.comp_apply, AlgHom.comp_apply]
      change (Algebra.TensorProduct.lift (AlgHom.id ℤ Coordinate)
          antipode _)
          (CoalgebraStruct.comul x13) =
        (Algebra.ofId ℤ Coordinate) (CoalgebraStruct.counit x13)
      rw [h13, e13]
      simp [antipode]
      ring

/-- The split upper-unitriangular affine group scheme over `Spec ℤ`. -/
noncomputable def schemeObject :
    Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of ℤ)) := by
  letI : HopfAlgebra ℤ Coordinate := hopfAlgebra
  exact affineGroupSchemeObject (CommRingCat.of ℤ)
    (CommRingCat.of Coordinate)

set_option linter.style.haveILetI false in
/-- The represented affine scheme carries the expected group-object
structure. -/
theorem schemeObject_hasGroupObject :
    Nonempty (GrpObj schemeObject) := by
  letI : HopfAlgebra ℤ Coordinate := hopfAlgebra
  simpa [schemeObject] using
    (affineGroupSchemeObject_hasGroupObject (CommRingCat.of ℤ)
      (CommRingCat.of Coordinate))

end

end UpperUnitriangularThree
end AlgebraicGeometry
end RiemannResearch
