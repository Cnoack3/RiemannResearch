/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Unit retracts and degree-one zero-cycle classes

This module isolates the exact abstract correspondence argument in
Proposition 4.8 of the user-provided 5 August 2026 Serre II manuscript. The
source supports the statement and proof strategy.

No category of Chow motives is constructed here. Instead,
`UnitRetractDegreeData` records precisely the needed input: zero-cycle
classes are maps from a distinguished unit object, maps back to the unit form
a rank-one integral group, and composition computes integer degree.

The reverse implication keeps track of the integral sign. An arbitrary
retraction initially gives degree `1` or `-1`; multiplying the cycle by the
integer coefficient of the reverse correspondence produces degree exactly
`1`.
-/

namespace RiemannResearch.Motives

open CategoryTheory

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {Z : Type w} [AddCommGroup Z]

/-- The exact correspondence data used to detect a unit-object retract.

The first equivalence identifies zero-cycle classes with maps from the unit.
The second is the geometrically-integral rank-one description of maps back to
the unit. The final equation is the composition-degree formula. -/
structure UnitRetractDegreeData (unitObj motive : C) (Z : Type w)
    [AddCommGroup Z] where
  zeroCycleHomEquiv : Z ≃+ (unitObj ⟶ motive)
  reverseRankEquiv : (motive ⟶ unitObj) ≃+ ℤ
  unitRankEquiv : (unitObj ⟶ unitObj) ≃+ ℤ
  unitRank_id : unitRankEquiv (𝟙 unitObj) = 1
  degree : Z →+ ℤ
  unitRank_comp :
    ∀ (z : Z) (r : motive ⟶ unitObj),
      unitRankEquiv (zeroCycleHomEquiv z ≫ r) =
        reverseRankEquiv r * degree z

/-- The distinguished unit object is a retract of `motive`. -/
def HasUnitRetract (unitObj motive : C) : Prop :=
  ∃ (i : unitObj ⟶ motive) (r : motive ⟶ unitObj),
    i ≫ r = 𝟙 unitObj

/-- The supplied zero-cycle group contains a class of degree one. -/
def HasDegreeOneZeroCycle {unitObj motive : C}
    (data : UnitRetractDegreeData unitObj motive Z) : Prop :=
  ∃ z : Z, data.degree z = 1

namespace UnitRetractDegreeData

variable {unitObj motive : C}
variable (data : UnitRetractDegreeData unitObj motive Z)

/-- The rank-one generator back to the unit. In the Chow-motive application
this is the structure morphism. -/
def structureMorphism : motive ⟶ unitObj :=
  data.reverseRankEquiv.symm 1

@[simp]
theorem reverseRankEquiv_structureMorphism :
    data.reverseRankEquiv data.structureMorphism = 1 :=
  data.reverseRankEquiv.apply_symm_apply 1

/-- The zero-cycle class represented by a map from the unit object. -/
def zeroCycleOfHom (i : unitObj ⟶ motive) : Z :=
  data.zeroCycleHomEquiv.symm i

@[simp]
theorem zeroCycleHomEquiv_zeroCycleOfHom (i : unitObj ⟶ motive) :
    data.zeroCycleHomEquiv (data.zeroCycleOfHom i) = i :=
  data.zeroCycleHomEquiv.apply_symm_apply i

/-- Correct the possible simultaneous minus signs in a retraction. -/
def signedZeroCycleOfRetract
    (i : unitObj ⟶ motive) (r : motive ⟶ unitObj) : Z :=
  data.reverseRankEquiv r • data.zeroCycleOfHom i

/-- A retraction gives the integer equation “reverse coefficient times degree
equals one.” -/
theorem rank_mul_degree_eq_one_of_retract
    {i : unitObj ⟶ motive} {r : motive ⟶ unitObj}
    (h : i ≫ r = 𝟙 unitObj) :
    data.reverseRankEquiv r * data.degree (data.zeroCycleOfHom i) = 1 := by
  calc
    data.reverseRankEquiv r * data.degree (data.zeroCycleOfHom i) =
        data.unitRankEquiv
          (data.zeroCycleHomEquiv (data.zeroCycleOfHom i) ≫ r) := by
      symm
      exact data.unitRank_comp (data.zeroCycleOfHom i) r
    _ = data.unitRankEquiv (i ≫ r) := by
      rw [data.zeroCycleHomEquiv_zeroCycleOfHom]
    _ = data.unitRankEquiv (𝟙 unitObj) := by rw [h]
    _ = 1 := data.unitRank_id

/-- Before correcting the sign, a retract gives degree `1` or `-1`. -/
theorem degree_zeroCycleOfHom_eq_one_or_neg_one_of_retract
    {i : unitObj ⟶ motive} {r : motive ⟶ unitObj}
    (h : i ≫ r = 𝟙 unitObj) :
    data.degree (data.zeroCycleOfHom i) = 1 ∨
      data.degree (data.zeroCycleOfHom i) = -1 := by
  exact Int.eq_one_or_neg_one_of_mul_eq_one
    (u := data.degree (data.zeroCycleOfHom i))
    (v := data.reverseRankEquiv r)
    (by
      simpa only [mul_comm] using
        data.rank_mul_degree_eq_one_of_retract h)

/-- Scaling by the reverse coefficient resolves the sign and gives degree
exactly one. -/
theorem degree_signedZeroCycleOfRetract
    {i : unitObj ⟶ motive} {r : motive ⟶ unitObj}
    (h : i ≫ r = 𝟙 unitObj) :
    data.degree (data.signedZeroCycleOfRetract i r) = 1 := by
  calc
    data.degree (data.signedZeroCycleOfRetract i r) =
        data.reverseRankEquiv r • data.degree (data.zeroCycleOfHom i) := by
      exact map_zsmul data.degree (data.reverseRankEquiv r)
        (data.zeroCycleOfHom i)
    _ = data.reverseRankEquiv r * data.degree (data.zeroCycleOfHom i) := by
      simp
    _ = 1 := data.rank_mul_degree_eq_one_of_retract h

/-- A degree-one zero-cycle supplies a splitting of the unit object. -/
theorem hasUnitRetract_of_degree_eq_one
    {z : Z} (hz : data.degree z = 1) :
    HasUnitRetract unitObj motive := by
  refine ⟨data.zeroCycleHomEquiv z, data.structureMorphism, ?_⟩
  apply data.unitRankEquiv.injective
  calc
    data.unitRankEquiv
        (data.zeroCycleHomEquiv z ≫ data.structureMorphism) =
        data.reverseRankEquiv data.structureMorphism * data.degree z :=
      data.unitRank_comp z data.structureMorphism
    _ = 1 := by simp [hz]
    _ = data.unitRankEquiv (𝟙 unitObj) := data.unitRank_id.symm

/-- A unit-object retract supplies a degree-one zero-cycle, with the integral
sign handled explicitly. -/
theorem hasDegreeOneZeroCycle_of_hasUnitRetract
    (h : HasUnitRetract unitObj motive) :
    HasDegreeOneZeroCycle data := by
  rcases h with ⟨i, r, hir⟩
  exact ⟨data.signedZeroCycleOfRetract i r,
    data.degree_signedZeroCycleOfRetract hir⟩

/-- Abstract correspondence form of Proposition 4.8. -/
theorem hasUnitRetract_iff_hasDegreeOneZeroCycle :
    HasUnitRetract unitObj motive ↔ HasDegreeOneZeroCycle data := by
  constructor
  · exact data.hasDegreeOneZeroCycle_of_hasUnitRetract
  · rintro ⟨z, hz⟩
    exact data.hasUnitRetract_of_degree_eq_one hz

end UnitRetractDegreeData

end RiemannResearch.Motives
