/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.ThreeQuaternionBrauerCompletion

/-!
# Quaternionic solutions of the affine E7 Brauer system

This module packages the exact converse to the affine construction in
`ThreeQuaternionBrauerCompletion`.

For a predicate `IsQuaternion` on an exponent-two additive class group, an
affine parameter `x` makes all four auxiliary classes quaternionic exactly when
the corresponding four-class package is a quaternionic solution of the three
prescribed pair-sum equations.  The inverse sends a solution to its first
class.  This identifies the precise remaining obstruction for the
four-quaternion orthogonal-sum mechanism.

The result is deliberately limited to that mechanism.  It does not assert that
such a parameter exists for every quaternion triple, and it does not identify
this affine completion problem with the full degree-eight quadratic-pair
realization problem in Gille's Question 8.3.4.
-/

namespace RiemannResearch.E7.ThreeQuaternionBrauerCompletion

variable {β : Type*} [AddCommGroup β]

/-- Every entry of a four-class package is represented by a quaternion algebra,
abstracted through the predicate `IsQuaternion`. -/
def AllQuaternion
    (IsQuaternion : β → Prop) (r : FourBrauerClasses β) : Prop :=
  IsQuaternion r.r1 ∧
  IsQuaternion r.r2 ∧
  IsQuaternion r.r3 ∧
  IsQuaternion r.r4

/-- On an affine four-class package, `AllQuaternion` is definitionally the
completion condition from the base module. -/
theorem allQuaternion_affineFourClasses_iff
    (IsQuaternion : β → Prop) (q1 q2 q3 x : β) :
    AllQuaternion IsQuaternion (affineFourClasses q1 q2 q3 x) ↔
      IsAffineQuaternionCompletion IsQuaternion q1 q2 q3 x := by
  rfl

/-- A quaternionic solution of the target pair-sum equations determines an
affine quaternion completion, with parameter equal to its first class. -/
theorem isAffineQuaternionCompletion_of_allQuaternion_targetPairSums
    (twoTorsion : ∀ z : β, z + z = 0)
    (IsQuaternion : β → Prop)
    (q1 q2 q3 : β) (r : FourBrauerClasses β)
    (hPair : HasTargetPairSums q1 q2 q3 r)
    (hQuaternion : AllQuaternion IsQuaternion r) :
    IsAffineQuaternionCompletion IsQuaternion q1 q2 q3 r.r1 := by
  have hr : r = affineFourClasses q1 q2 q3 r.r1 :=
    eq_affineFourClasses_of_hasTargetPairSums
      twoTorsion q1 q2 q3 r hPair
  change AllQuaternion IsQuaternion (affineFourClasses q1 q2 q3 r.r1)
  simpa [hr] using hQuaternion

/-- Affine quaternion-completion parameters are canonically equivalent to
quaternionic solutions of the three target pair-sum equations. -/
def affineQuaternionCompletionEquiv
    (twoTorsion : ∀ z : β, z + z = 0)
    (IsQuaternion : β → Prop) (q1 q2 q3 : β) :
    {x : β // IsAffineQuaternionCompletion IsQuaternion q1 q2 q3 x} ≃
      {r : FourBrauerClasses β //
        HasTargetPairSums q1 q2 q3 r ∧ AllQuaternion IsQuaternion r} where
  toFun x :=
    ⟨affineFourClasses q1 q2 q3 x.1,
      ⟨affineFourClasses_hasTargetPairSums
          twoTorsion q1 q2 q3 x.1,
        (allQuaternion_affineFourClasses_iff
          IsQuaternion q1 q2 q3 x.1).2 x.2⟩⟩
  invFun r :=
    ⟨r.1.r1,
      isAffineQuaternionCompletion_of_allQuaternion_targetPairSums
        twoTorsion IsQuaternion q1 q2 q3 r.1 r.2.1 r.2.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv r := by
    apply Subtype.ext
    exact (eq_affineFourClasses_of_hasTargetPairSums
      twoTorsion q1 q2 q3 r.1 r.2.1).symm

/-- Existence of an affine quaternion-completion parameter is exactly existence
of a quaternionic four-class solution of the prescribed pair-sum system. -/
theorem exists_affineQuaternionCompletion_iff_exists_quaternionicTargetPairSums
    (twoTorsion : ∀ z : β, z + z = 0)
    (IsQuaternion : β → Prop) (q1 q2 q3 : β) :
    (∃ x : β, IsAffineQuaternionCompletion IsQuaternion q1 q2 q3 x) ↔
      ∃ r : FourBrauerClasses β,
        HasTargetPairSums q1 q2 q3 r ∧ AllQuaternion IsQuaternion r := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨affineFourClasses q1 q2 q3 x,
      affineFourClasses_hasTargetPairSums twoTorsion q1 q2 q3 x,
      (allQuaternion_affineFourClasses_iff
        IsQuaternion q1 q2 q3 x).2 hx⟩
  · rintro ⟨r, hPair, hQuaternion⟩
    exact ⟨r.r1,
      isAffineQuaternionCompletion_of_allQuaternion_targetPairSums
        twoTorsion IsQuaternion q1 q2 q3 r hPair hQuaternion⟩

end RiemannResearch.E7.ThreeQuaternionBrauerCompletion
