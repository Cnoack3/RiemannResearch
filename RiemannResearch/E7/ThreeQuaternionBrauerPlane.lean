/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.ThreeQuaternionBrauerCompletion

/-!
# The affine Brauer plane behind the E7 three-quaternion construction

The four auxiliary classes in the additive four-quaternion construction are
not an arbitrary tuple.  They are a translate of the direction packet

```
(0, q2 + q3, q1 + q2, q1 + q3).
```

Over an exponent-two class group, its three nonzero entries satisfy the
Klein-four relation: the sum of any two is the third.  Thus the remaining
representability target for this construction is exactly the existence of a
translate all four of whose entries are quaternion classes.

The natural translate by `q1` has entries

```
(q1, q1 + q2 + q3, q2, q3).
```

Consequently, when the three inputs are already quaternion classes, the only
extra condition for this particular translate is quaternion representability
of the triple sum.  This does not imply that the natural translate is the only
possible completion, and this file does not assert existence of any
quaternionic translate.
-/

namespace RiemannResearch.E7.ThreeQuaternionBrauerPlane

open RiemannResearch.E7.ThreeQuaternionBrauerCompletion

variable {β : Type*} [AddCommGroup β]

/-- Translate all four entries of an auxiliary class packet by the same
class. -/
def translateFourClasses (t : β) (r : FourBrauerClasses β) :
    FourBrauerClasses β where
  r1 := t + r.r1
  r2 := t + r.r2
  r3 := t + r.r3
  r4 := t + r.r4

/-- Translation of an affine packet adds the translation class to its affine
parameter. -/
theorem translateFourClasses_affineFourClasses
    (t q1 q2 q3 x : β) :
    translateFourClasses t (affineFourClasses q1 q2 q3 x) =
      affineFourClasses q1 q2 q3 (t + x) := by
  ext <;> simp [translateFourClasses, affineFourClasses, add_assoc]

/-- The direction packet of the affine plane. -/
def directionFourClasses (q1 q2 q3 : β) : FourBrauerClasses β :=
  affineFourClasses q1 q2 q3 0

/-- Every affine solution is a translate of the direction packet. -/
theorem translate_directionFourClasses
    (q1 q2 q3 x : β) :
    translateFourClasses x (directionFourClasses q1 q2 q3) =
      affineFourClasses q1 q2 q3 x := by
  simpa [directionFourClasses] using
    (translateFourClasses_affineFourClasses x q1 q2 q3 0)

/-- In exponent two, the second plus the third direction is the fourth. -/
theorem direction_r2_add_r3_eq_r4
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 : β) :
    let d := directionFourClasses q1 q2 q3
    d.r2 + d.r3 = d.r4 := by
  change (q2 + q3) + (q1 + q2) = q1 + q3
  calc
    (q2 + q3) + (q1 + q2) = q1 + (q2 + q2) + q3 := by abel
    _ = q1 + q3 := by rw [twoTorsion q2]; simp

/-- In exponent two, the second plus the fourth direction is the third. -/
theorem direction_r2_add_r4_eq_r3
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 : β) :
    let d := directionFourClasses q1 q2 q3
    d.r2 + d.r4 = d.r3 := by
  change (q2 + q3) + (q1 + q3) = q1 + q2
  calc
    (q2 + q3) + (q1 + q3) = q1 + q2 + (q3 + q3) := by abel
    _ = q1 + q2 := by rw [twoTorsion q3]; simp

/-- In exponent two, the third plus the fourth direction is the second. -/
theorem direction_r3_add_r4_eq_r2
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 : β) :
    let d := directionFourClasses q1 q2 q3
    d.r3 + d.r4 = d.r2 := by
  change (q1 + q2) + (q1 + q3) = q2 + q3
  calc
    (q1 + q2) + (q1 + q3) = (q1 + q1) + (q2 + q3) := by abel
    _ = q2 + q3 := by rw [twoTorsion q1]; simp

/-- The natural packet is the translate whose first entry is `q1`. -/
def naturalFourClasses (q1 q2 q3 : β) : FourBrauerClasses β :=
  affineFourClasses q1 q2 q3 q1

/-- The natural translate contains the three input classes and the triple
sum. -/
theorem naturalFourClasses_coordinates
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 : β) :
    naturalFourClasses q1 q2 q3 =
      { r1 := q1
        r2 := q1 + q2 + q3
        r3 := q2
        r4 := q3 } := by
  ext
  · rfl
  · rfl
  · change q1 + q1 + q2 = q2
    rw [twoTorsion q1]
    simp
  · change q1 + q1 + q3 = q3
    rw [twoTorsion q1]
    simp

/-- Every affine packet is a translate of the natural packet. -/
theorem affineFourClasses_eq_translate_naturalFourClasses
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 x : β) :
    affineFourClasses q1 q2 q3 x =
      translateFourClasses (x + q1) (naturalFourClasses q1 q2 q3) := by
  change affineFourClasses q1 q2 q3 x =
    translateFourClasses (x + q1) (affineFourClasses q1 q2 q3 q1)
  have hx : (x + q1) + q1 = x := by
    calc
      (x + q1) + q1 = x + (q1 + q1) := by abel
      _ = x := by rw [twoTorsion q1]; simp
  have h := translateFourClasses_affineFourClasses
    (x + q1) q1 q2 q3 q1
  rw [hx] at h
  exact h.symm

/-- A quaternionic translate of the prescribed direction packet. -/
def HasQuaternionicTranslate
    (IsQuaternion : β → Prop) (q1 q2 q3 : β) : Prop :=
  ∃ x : β,
    AllQuaternionClasses IsQuaternion
      (translateFourClasses x (directionFourClasses q1 q2 q3))

/-- The affine-completion target is exactly existence of a quaternionic
translate of the direction packet. -/
theorem exists_affineQuaternionCompletion_iff_hasQuaternionicTranslate
    (IsQuaternion : β → Prop) (q1 q2 q3 : β) :
    (∃ x : β,
      IsAffineQuaternionCompletion IsQuaternion q1 q2 q3 x) ↔
      HasQuaternionicTranslate IsQuaternion q1 q2 q3 := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [translate_directionFourClasses]
    simpa [AllQuaternionClasses, IsAffineQuaternionCompletion,
      affineFourClasses] using hx
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [translate_directionFourClasses] at hx
    simpa [AllQuaternionClasses, IsAffineQuaternionCompletion,
      affineFourClasses] using hx

/-- At the natural parameter `q1`, quaternion completion is exactly
quaternion representability of the three inputs and their triple sum. -/
theorem affineQuaternionCompletion_at_q1_iff
    (twoTorsion : ∀ z : β, z + z = 0)
    (IsQuaternion : β → Prop)
    (q1 q2 q3 : β) :
    IsAffineQuaternionCompletion IsQuaternion q1 q2 q3 q1 ↔
      IsQuaternion q1 ∧
      IsQuaternion (q1 + q2 + q3) ∧
      IsQuaternion q2 ∧
      IsQuaternion q3 := by
  have h2 : q1 + q1 + q2 = q2 := by
    rw [twoTorsion q1]
    simp
  have h3 : q1 + q1 + q3 = q3 := by
    rw [twoTorsion q1]
    simp
  simp only [IsAffineQuaternionCompletion]
  rw [h2, h3]

/-- If the three inputs are quaternion classes, the only additional condition
for the natural translate is quaternion representability of their triple
sum. -/
theorem affineQuaternionCompletion_at_q1_iff_tripleSum
    (twoTorsion : ∀ z : β, z + z = 0)
    (IsQuaternion : β → Prop)
    {q1 q2 q3 : β}
    (hq1 : IsQuaternion q1)
    (hq2 : IsQuaternion q2)
    (hq3 : IsQuaternion q3) :
    IsAffineQuaternionCompletion IsQuaternion q1 q2 q3 q1 ↔
      IsQuaternion (q1 + q2 + q3) := by
  rw [affineQuaternionCompletion_at_q1_iff
    twoTorsion IsQuaternion q1 q2 q3]
  constructor
  · intro h
    exact h.2.1
  · intro h
    exact ⟨hq1, h, hq2, hq3⟩

end RiemannResearch.E7.ThreeQuaternionBrauerPlane
