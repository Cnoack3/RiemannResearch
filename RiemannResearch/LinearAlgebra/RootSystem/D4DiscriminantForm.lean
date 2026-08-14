/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import RiemannResearch.LinearAlgebra.RootSystem.D4Discriminant

/-!
# The quadratic form on the D4 discriminant group

This file equips the coordinate presentation
`P / Q ≃ (ZMod 2) × (ZMod 2)` with its D4 discriminant quadratic form.
In parity coordinates it is

`q(a, b) = a + b + a * b`,

so every nonzero class has value one. Its polarization is the nondegenerate
alternating pairing

`B((a, b), (c, d)) = a * d + b * c`.

The displayed inverse Cartan matrix proves that this finite formula is the
reduction modulo two of the integral D4 weight norm. Thus it is not merely an
abstract four-element quadratic space: it is the discriminant form arising
from the based root and weight lattices in `D4Lattice`.

These are the exact finite quadratic data needed for D4-by-D4 gluing. They do
not construct an E8 identification, a Spin(8) group scheme, or half-spin
representations.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

noncomputable section

/-- The D4 discriminant quadratic form in parity coordinates. -/
def discriminantQuadraticModel (x : DiscriminantModel) : ZMod 2 :=
  x.1 + x.2 + x.1 * x.2

/-- The polarization of the D4 discriminant quadratic form. -/
def discriminantBilinearModel
    (x y : DiscriminantModel) : ZMod 2 :=
  x.1 * y.2 + x.2 * y.1

/-- The polarized pairing, packaged as an actual bilinear form over
`ZMod 2`. -/
def discriminantBilinearFormModel :
    LinearMap.BilinForm (ZMod 2) DiscriminantModel :=
  LinearMap.mk₂ (ZMod 2)
    discriminantBilinearModel
    (by decide) (by decide) (by decide) (by decide)

/-- The parity-coordinate formula, packaged as an actual quadratic form over
`ZMod 2`. -/
def discriminantQuadraticFormModel :
    QuadraticForm (ZMod 2) DiscriminantModel :=
  QuadraticMap.mk
    discriminantQuadraticModel
    (by decide)
    ⟨discriminantBilinearFormModel, by decide⟩

@[simp]
theorem discriminantBilinearFormModel_apply
    (x y : DiscriminantModel) :
    discriminantBilinearFormModel x y =
      discriminantBilinearModel x y :=
  rfl

@[simp]
theorem discriminantQuadraticFormModel_apply
    (x : DiscriminantModel) :
    discriminantQuadraticFormModel x =
      discriminantQuadraticModel x :=
  rfl

/-- The rational D4 Cartan matrix in the published
`V, central, S+, S-` order. -/
def cartanRat : Matrix (Fin 4) (Fin 4) ℚ :=
  cartanFinFour.map (Int.castRingHom ℚ)

/-- The displayed rational Cartan matrix, used as a finite certificate. -/
def cartanRatDisplayed : Matrix (Fin 4) (Fin 4) ℚ :=
  ![
    ![2, -1, 0, 0],
    ![-1, 2, -1, -1],
    ![0, -1, 2, 0],
    ![0, -1, 0, 2]
  ]

theorem cartanRat_eq_displayed :
    cartanRat = cartanRatDisplayed := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartanRat, cartanRatDisplayed, cartanFinFour,
      finFourEquivNode, cartan]

/-- The inverse D4 Cartan matrix over the rationals. -/
def inverseCartanRat : Matrix (Fin 4) (Fin 4) ℚ :=
  ![
    ![1, 1, 1 / 2, 1 / 2],
    ![1, 2, 1, 1],
    ![1 / 2, 1, 1, 1 / 2],
    ![1 / 2, 1, 1 / 2, 1]
  ]

theorem cartanRat_mul_inverseCartanRat :
    cartanRat * inverseCartanRat = 1 := by
  rw [cartanRat_eq_displayed]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [cartanRatDisplayed, inverseCartanRat,
      Fin.sum_univ_succ]

theorem inverseCartanRat_mul_cartanRat :
    inverseCartanRat * cartanRat = 1 := by
  rw [cartanRat_eq_displayed]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [cartanRatDisplayed, inverseCartanRat,
      Fin.sum_univ_succ]

/-- The rational weight-lattice pairing `xᵀ A⁻¹ y`. -/
def weightPairing (x y : WeightCoordinates) : ℚ :=
  dotProduct (fun i => (x i : ℚ))
    (inverseCartanRat.mulVec (fun i => (y i : ℚ)))

/-- The integral norm polynomial on D4 weight coordinates. Its rational cast
is the self-pairing defined by `inverseCartanRat`. -/
def weightNorm (x : WeightCoordinates) : ℤ :=
  x 0 * x 0 + 2 * x 1 * x 1 + x 2 * x 2 + x 3 * x 3 +
    2 * x 0 * x 1 + x 0 * x 2 + x 0 * x 3 +
    2 * x 1 * x 2 + 2 * x 1 * x 3 + x 2 * x 3

theorem weightPairing_self_eq_weightNorm
    (x : WeightCoordinates) :
    weightPairing x x = (weightNorm x : ℚ) := by
  simp [weightPairing, inverseCartanRat, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, weightNorm]
  ring

/-- Reduction of the inverse-Cartan norm modulo two is exactly the
parity-coordinate discriminant form. -/
theorem weightNorm_modTwo_eq_discriminantQuadraticModel_parityMap
    (x : WeightCoordinates) :
    ((weightNorm x : ℤ) : ZMod 2) =
      discriminantQuadraticModel (parityMap x) := by
  simp only [weightNorm, Fin.isValue, Int.cast_add, Int.cast_mul,
    Int.cast_ofNat, discriminantQuadraticModel, parityMap,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have htwo : (2 : ZMod 2) = 0 := by
    decide
  have hsquare : ∀ a : ZMod 2, a * a = a := by
    decide
  ring_nf
  simp [htwo, pow_two, hsquare]
  ring

/-- The D4 root lattice is even for the inverse-Cartan weight norm. -/
theorem two_dvd_weightNorm_cartanMap
    (x : RootCoordinates) :
    (2 : ℤ) ∣ weightNorm (cartanMap x) := by
  apply
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (weightNorm (cartanMap x)) 2).mp
  rw [weightNorm_modTwo_eq_discriminantQuadraticModel_parityMap,
    parityMap_cartanMap]
  rfl

theorem discriminantQuadraticModel_eq_zero_iff
    (x : DiscriminantModel) :
    discriminantQuadraticModel x = 0 ↔ x = 0 := by
  revert x
  decide

theorem discriminantQuadraticModel_label
    (label : TrialityLabel) :
    discriminantQuadraticModel (labelParity label) = 1 := by
  cases label <;> decide

theorem discriminantQuadraticModel_add
    (x y : DiscriminantModel) :
    discriminantQuadraticModel (x + y) =
      discriminantQuadraticModel x +
        discriminantQuadraticModel y +
          discriminantBilinearModel x y := by
  revert x y
  decide

theorem discriminantBilinearModel_add_left
    (x y z : DiscriminantModel) :
    discriminantBilinearModel (x + y) z =
      discriminantBilinearModel x z +
        discriminantBilinearModel y z := by
  revert x y z
  decide

theorem discriminantBilinearModel_add_right
    (x y z : DiscriminantModel) :
    discriminantBilinearModel x (y + z) =
      discriminantBilinearModel x y +
        discriminantBilinearModel x z := by
  revert x y z
  decide

theorem discriminantBilinearModel_symmetric
    (x y : DiscriminantModel) :
    discriminantBilinearModel x y =
      discriminantBilinearModel y x := by
  revert x y
  decide

theorem discriminantBilinearModel_nondegenerate
    (x : DiscriminantModel) :
    (∀ y, discriminantBilinearModel x y = 0) ↔ x = 0 := by
  revert x
  decide

theorem discriminantQuadraticModel_action
    (σ : DiagramSymmetry) (x : DiscriminantModel) :
    discriminantQuadraticModel (modelAction σ x) =
      discriminantQuadraticModel x := by
  revert σ x
  decide

theorem discriminantBilinearModel_action
    (σ : DiagramSymmetry) (x y : DiscriminantModel) :
    discriminantBilinearModel (modelAction σ x) (modelAction σ y) =
      discriminantBilinearModel x y := by
  revert σ x y
  decide

/-- The D4 discriminant quadratic form on `P / Q`. -/
def discriminantQuadratic (x : DiscriminantGroup) : ZMod 2 :=
  discriminantQuadraticModel (discriminantEquivParity x)

/-- The associated symmetric bilinear pairing on `P / Q`. -/
def discriminantBilinear
    (x y : DiscriminantGroup) : ZMod 2 :=
  discriminantBilinearModel
    (discriminantEquivParity x) (discriminantEquivParity y)

/-- The quotient discriminant form is represented by the inverse-Cartan norm
of every weight-coordinate representative. -/
@[simp]
theorem discriminantQuadratic_mk
    (x : WeightCoordinates) :
    discriminantQuadratic
        (QuotientAddGroup.mk' rootSublattice x) =
      ((weightNorm x : ℤ) : ZMod 2) := by
  rw [discriminantQuadratic, discriminantEquivParity_mk,
    ← weightNorm_modTwo_eq_discriminantQuadraticModel_parityMap]

@[simp]
theorem discriminantQuadratic_eq_zero_iff
    (x : DiscriminantGroup) :
    discriminantQuadratic x = 0 ↔ x = 0 := by
  rw [discriminantQuadratic, discriminantQuadraticModel_eq_zero_iff]
  exact discriminantEquivParity.map_eq_zero_iff

@[simp]
theorem discriminantQuadratic_fundamentalClass
    (label : TrialityLabel) :
    discriminantQuadratic (fundamentalClass label) = 1 := by
  rw [discriminantQuadratic, discriminantEquivParity_fundamentalClass]
  exact discriminantQuadraticModel_label label

theorem discriminantQuadratic_add
    (x y : DiscriminantGroup) :
    discriminantQuadratic (x + y) =
      discriminantQuadratic x + discriminantQuadratic y +
        discriminantBilinear x y := by
  rw [discriminantQuadratic, discriminantQuadratic,
    discriminantQuadratic, discriminantBilinear,
    discriminantEquivParity.map_add]
  exact discriminantQuadraticModel_add _ _

theorem discriminantBilinear_add_left
    (x y z : DiscriminantGroup) :
    discriminantBilinear (x + y) z =
      discriminantBilinear x z + discriminantBilinear y z := by
  rw [discriminantBilinear, discriminantBilinear,
    discriminantBilinear, discriminantEquivParity.map_add]
  exact discriminantBilinearModel_add_left _ _ _

theorem discriminantBilinear_add_right
    (x y z : DiscriminantGroup) :
    discriminantBilinear x (y + z) =
      discriminantBilinear x y + discriminantBilinear x z := by
  rw [discriminantBilinear, discriminantBilinear,
    discriminantBilinear, discriminantEquivParity.map_add]
  exact discriminantBilinearModel_add_right _ _ _

theorem discriminantBilinear_symmetric
    (x y : DiscriminantGroup) :
    discriminantBilinear x y = discriminantBilinear y x := by
  exact discriminantBilinearModel_symmetric _ _

/-- The polarization of the D4 discriminant form has zero radical. -/
theorem discriminantBilinear_nondegenerate
    (x : DiscriminantGroup) :
    (∀ y, discriminantBilinear x y = 0) ↔ x = 0 := by
  constructor
  · intro h
    apply discriminantEquivParity.injective
    apply (discriminantBilinearModel_nondegenerate
      (discriminantEquivParity x)).1
    intro y
    obtain ⟨z, rfl⟩ := discriminantEquivParity.surjective y
    exact h z
  · rintro rfl y
    simp [discriminantBilinear, discriminantBilinearModel]

/-- Every diagram symmetry preserves the D4 discriminant quadratic form. -/
theorem discriminantQuadratic_action
    (σ : DiagramSymmetry) (x : DiscriminantGroup) :
    discriminantQuadratic (discriminantAction σ x) =
      discriminantQuadratic x := by
  change
    discriminantQuadraticModel
        (discriminantEquivParity (discriminantActionPerm σ x)) =
      discriminantQuadraticModel (discriminantEquivParity x)
  rw [discriminantEquivParity_discriminantActionPerm_apply]
  exact discriminantQuadraticModel_action σ _

/-- Every diagram symmetry preserves the polarized discriminant pairing. -/
theorem discriminantBilinear_action
    (σ : DiagramSymmetry) (x y : DiscriminantGroup) :
    discriminantBilinear
        (discriminantAction σ x) (discriminantAction σ y) =
      discriminantBilinear x y := by
  change
    discriminantBilinearModel
        (discriminantEquivParity (discriminantActionPerm σ x))
        (discriminantEquivParity (discriminantActionPerm σ y)) =
      discriminantBilinearModel
        (discriminantEquivParity x) (discriminantEquivParity y)
  rw [discriminantEquivParity_discriminantActionPerm_apply,
    discriminantEquivParity_discriminantActionPerm_apply]
  exact discriminantBilinearModel_action σ _ _

/-- Distinct outer fundamental classes pair to one; each class pairs with
itself to zero. -/
theorem discriminantBilinear_fundamentalClass
    (a b : TrialityLabel) :
    discriminantBilinear (fundamentalClass a) (fundamentalClass b) =
      if a = b then 0 else 1 := by
  rw [discriminantBilinear,
    discriminantEquivParity_fundamentalClass,
    discriminantEquivParity_fundamentalClass]
  cases a <;> cases b <;> decide

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
