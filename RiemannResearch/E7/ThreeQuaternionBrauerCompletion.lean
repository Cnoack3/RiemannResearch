/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Tactic.Abel

/-!
# Affine Brauer bookkeeping for the E7 three-quaternion problem

Gille's Question 8.3.4 asks whether three quaternion algebras can always be
realized as the triality-related Tits data of a degree-eight algebra with
quadratic pair. Proposition 5.4 of Dolphin--Quéguiner-Mathieu gives one
explicit construction from four quaternion algebras whose tensor product is
split: if their Brauer classes are `r1`, `r2`, `r3`, and `r4`, the three
underlying trialitarian classes are the corresponding pair sums.

This module isolates the exact exponent-two additive calculation behind that
construction. For prescribed quaternion classes `q1`, `q2`, and `q3`, all
solutions of

* `r1 + r2 = q2 + q3`,
* `r1 + r3 = q1 + q2`, and
* `r1 + r4 = q1 + q3`

are uniquely parametrized by one class `x = r1`:

```
(r1, r2, r3, r4) =
  (x, x + q2 + q3, x + q1 + q2, x + q1 + q3).
```

The complementary pair sums and the vanishing of the total class then follow
formally. The remaining mathematical obstruction is not additive: one must
choose `x` so that all four displayed classes are represented by quaternion
algebras. Nothing in this file asserts that such an `x` always exists, and it
does not construct a central simple algebra, a quadratic pair, or an E7
torsor. Thus it is an unconditional algebraic certificate for one proposed
construction mechanism, not a proof of Gille's question or of Serre II for E7.

Sources supporting the trialitarian interpretation:

* P. Gille, *Groupes algébriques semi-simples en dimension cohomologique
  inférieure ou égale à 2*, LNM 2238 (2019), Question 8.3.4 and
  Proposition 8.3.6, <https://doi.org/10.1007/978-3-030-17272-5>.
* A. Dolphin and A. Quéguiner-Mathieu, *The canonical quadratic pair on a
  Clifford algebra and triality*, Proposition 5.4,
  <https://arxiv.org/abs/1905.12526>.
-/

namespace RiemannResearch.E7.ThreeQuaternionBrauerCompletion

/-- Four additive classes used as inputs to the four-quaternion orthogonal-sum
construction. -/
@[ext]
structure FourBrauerClasses (β : Type*) where
  r1 : β
  r2 : β
  r3 : β
  r4 : β

variable {β : Type*} [AddCommGroup β]

/-- The affine four-class package attached to a parameter `x` and three target
quaternion classes. -/
def affineFourClasses (q1 q2 q3 x : β) : FourBrauerClasses β where
  r1 := x
  r2 := x + q2 + q3
  r3 := x + q1 + q2
  r4 := x + q1 + q3

/-- The three pair-sum equations in which the first auxiliary class is
distinguished. -/
def HasTargetPairSums (q1 q2 q3 : β) (r : FourBrauerClasses β) : Prop :=
  r.r1 + r.r2 = q2 + q3 ∧
  r.r1 + r.r3 = q1 + q2 ∧
  r.r1 + r.r4 = q1 + q3

/-- The three complementary pair-sum equations predicted by triality. -/
def HasOppositeTargetPairSums
    (q1 q2 q3 : β) (r : FourBrauerClasses β) : Prop :=
  r.r3 + r.r4 = q2 + q3 ∧
  r.r2 + r.r4 = q1 + q2 ∧
  r.r2 + r.r3 = q1 + q3

/-- In an exponent-two abelian group, one may solve `x + y = t` as
`y = x + t`. -/
lemma solve_second_of_add_eq
    (twoTorsion : ∀ z : β, z + z = 0)
    {x y t : β} (h : x + y = t) :
    y = x + t := by
  calc
    y = 0 + y := by simp
    _ = (x + x) + y := by rw [twoTorsion x]
    _ = x + (x + y) := by abel
    _ = x + t := by rw [h]

/-- Every affine four-class package has the three required distinguished pair
sums. -/
theorem affineFourClasses_hasTargetPairSums
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 x : β) :
    HasTargetPairSums q1 q2 q3 (affineFourClasses q1 q2 q3 x) := by
  refine ⟨?_, ?_, ?_⟩
  · change x + (x + q2 + q3) = q2 + q3
    calc
      x + (x + q2 + q3) = (x + x) + (q2 + q3) := by abel
      _ = q2 + q3 := by rw [twoTorsion x]; simp
  · change x + (x + q1 + q2) = q1 + q2
    calc
      x + (x + q1 + q2) = (x + x) + (q1 + q2) := by abel
      _ = q1 + q2 := by rw [twoTorsion x]; simp
  · change x + (x + q1 + q3) = q1 + q3
    calc
      x + (x + q1 + q3) = (x + x) + (q1 + q3) := by abel
      _ = q1 + q3 := by rw [twoTorsion x]; simp

/-- The displayed affine form is forced by the three distinguished pair-sum
equations. -/
theorem eq_affineFourClasses_of_hasTargetPairSums
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 : β) (r : FourBrauerClasses β)
    (h : HasTargetPairSums q1 q2 q3 r) :
    r = affineFourClasses q1 q2 q3 r.r1 := by
  rcases h with ⟨h12, h13, h14⟩
  ext
  · rfl
  · simpa [affineFourClasses, add_assoc] using
      (solve_second_of_add_eq twoTorsion h12)
  · simpa [affineFourClasses, add_assoc] using
      (solve_second_of_add_eq twoTorsion h13)
  · simpa [affineFourClasses, add_assoc] using
      (solve_second_of_add_eq twoTorsion h14)

/-- The solution set of the three pair-sum equations is canonically an affine
copy of the exponent-two class group, with inverse given by the first class. -/
def targetPairSumSolutionEquiv
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 : β) :
    β ≃ {r : FourBrauerClasses β // HasTargetPairSums q1 q2 q3 r} where
  toFun x := ⟨affineFourClasses q1 q2 q3 x,
    affineFourClasses_hasTargetPairSums twoTorsion q1 q2 q3 x⟩
  invFun r := r.1.r1
  left_inv x := rfl
  right_inv r := by
    apply Subtype.ext
    exact (eq_affineFourClasses_of_hasTargetPairSums
      twoTorsion q1 q2 q3 r.1 r.2).symm

/-- The three target trialitarian classes have zero total class. -/
theorem targetPairSums_sum_eq_zero
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 : β) :
    (q2 + q3) + (q1 + q2) + (q1 + q3) = 0 := by
  calc
    (q2 + q3) + (q1 + q2) + (q1 + q3) =
        (q1 + q1) + (q2 + q2) + (q3 + q3) := by abel
    _ = 0 := by
      rw [twoTorsion q1, twoTorsion q2, twoTorsion q3]
      simp

/-- Every affine solution also has the three complementary pair sums. -/
theorem affineFourClasses_hasOppositeTargetPairSums
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 x : β) :
    HasOppositeTargetPairSums q1 q2 q3
      (affineFourClasses q1 q2 q3 x) := by
  refine ⟨?_, ?_, ?_⟩
  · change (x + q1 + q2) + (x + q1 + q3) = q2 + q3
    calc
      (x + q1 + q2) + (x + q1 + q3) =
          (x + x) + (q1 + q1) + (q2 + q3) := by abel
      _ = q2 + q3 := by rw [twoTorsion x, twoTorsion q1]; simp
  · change (x + q2 + q3) + (x + q1 + q3) = q1 + q2
    calc
      (x + q2 + q3) + (x + q1 + q3) =
          (x + x) + (q3 + q3) + (q1 + q2) := by abel
      _ = q1 + q2 := by rw [twoTorsion x, twoTorsion q3]; simp
  · change (x + q2 + q3) + (x + q1 + q2) = q1 + q3
    calc
      (x + q2 + q3) + (x + q1 + q2) =
          (x + x) + (q2 + q2) + (q1 + q3) := by abel
      _ = q1 + q3 := by rw [twoTorsion x, twoTorsion q2]; simp

/-- The complementary equations follow from the distinguished equations, so
they impose no additional additive constraint. -/
theorem hasOppositeTargetPairSums_of_hasTargetPairSums
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 : β) (r : FourBrauerClasses β)
    (h : HasTargetPairSums q1 q2 q3 r) :
    HasOppositeTargetPairSums q1 q2 q3 r := by
  rw [eq_affineFourClasses_of_hasTargetPairSums
    twoTorsion q1 q2 q3 r h]
  exact affineFourClasses_hasOppositeTargetPairSums
    twoTorsion q1 q2 q3 r.r1

/-- The tensor product of the four auxiliary classes is split at the level of
the Brauer group. -/
theorem affineFourClasses_sum_eq_zero
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 x : β) :
    let r := affineFourClasses q1 q2 q3 x
    r.r1 + r.r2 + r.r3 + r.r4 = 0 := by
  change x + (x + q2 + q3) + (x + q1 + q2) + (x + q1 + q3) = 0
  calc
    x + (x + q2 + q3) + (x + q1 + q2) + (x + q1 + q3) =
        (x + x) + (x + x) + (q1 + q1) + (q2 + q2) + (q3 + q3) := by
      abel
    _ = 0 := by
      rw [twoTorsion x, twoTorsion q1, twoTorsion q2, twoTorsion q3]
      simp

/-- The condition that all four affine classes are represented by quaternion
algebras, abstracted as an arbitrary class predicate. -/
def IsAffineQuaternionCompletion
    (IsQuaternion : β → Prop) (q1 q2 q3 x : β) : Prop :=
  IsQuaternion x ∧
  IsQuaternion (x + q2 + q3) ∧
  IsQuaternion (x + q1 + q2) ∧
  IsQuaternion (x + q1 + q3)

/-- One sufficient stratum: if the total class `q1 + q2 + q3` is itself
quaternion-representable, the choice `x = q1` gives an affine completion. -/
theorem affineQuaternionCompletion_of_tripleSum
    (twoTorsion : ∀ z : β, z + z = 0)
    (IsQuaternion : β → Prop)
    {q1 q2 q3 : β}
    (hq1 : IsQuaternion q1)
    (hq2 : IsQuaternion q2)
    (hq3 : IsQuaternion q3)
    (h123 : IsQuaternion (q1 + q2 + q3)) :
    IsAffineQuaternionCompletion IsQuaternion q1 q2 q3 q1 := by
  refine ⟨hq1, h123, ?_, ?_⟩
  · simpa [twoTorsion q1]
  · simpa [twoTorsion q1]

/-- A second sufficient stratum: if all three pair sums are quaternion-
representable, the neutral parameter gives an affine completion. The explicit
`hzero` hypothesis records that the neutral class is represented by the split
quaternion algebra in the intended Brauer-group application. -/
theorem affineQuaternionCompletion_of_pairSums
    (IsQuaternion : β → Prop)
    {q1 q2 q3 : β}
    (hzero : IsQuaternion 0)
    (h23 : IsQuaternion (q2 + q3))
    (h12 : IsQuaternion (q1 + q2))
    (h13 : IsQuaternion (q1 + q3)) :
    IsAffineQuaternionCompletion IsQuaternion q1 q2 q3 0 := by
  refine ⟨hzero, ?_, ?_, ?_⟩
  · simpa
  · simpa
  · simpa

end RiemannResearch.E7.ThreeQuaternionBrauerCompletion
