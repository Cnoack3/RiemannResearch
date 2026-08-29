/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.ThreeQuaternionBrauerCompletion

/-!
# The pairwise Brauer-class target for inner D4 triality

For three exponent-two classes `q1`, `q2`, and `q3`, the three triality-related
classes occurring in Gille's E7 realization problem are

```
(q2 + q3, q1 + q2, q1 + q3).
```

This module proves the exact additive geometry of that map.  Its image is the
sum-zero plane, and each nonempty fiber is an affine copy of the original
class group: two triples have the same target exactly when one is obtained
from the other by adding one common class to all three entries.

For the intended application, the ambient exponent-two group is a 2-primary
Brauer-class group and the inputs are classes represented by quaternion
algebras.  The statements here deliberately do not assert that a common
translate preserves quaternion representability, nor do they construct a
quadratic pair or a trialitarian triple.  They identify the special central
cohomology locus on which the genuine nonabelian D4 realization obstruction
must be studied.
-/

namespace RiemannResearch.E7.TrialityBrauerTarget

open RiemannResearch.E7.ThreeQuaternionBrauerCompletion

/-- Three source classes whose pairwise sums are the desired trialitarian
Tits classes. -/
@[ext]
structure ThreeClasses (β : Type*) where
  q1 : β
  q2 : β
  q3 : β

/-- The three labelled classes attached to the vector and two half-spin
characters of the center of a simply connected group of type D4. -/
@[ext]
structure Target (β : Type*) where
  b23 : β
  b12 : β
  b13 : β

variable {β : Type*} [AddCommGroup β]

/-- The admissibility relation among the three nontrivial central characters:
the sum of the three labelled classes is zero. -/
def Target.IsAdmissible (t : Target β) : Prop :=
  t.b23 + t.b12 + t.b13 = 0

/-- Send three classes to their three pairwise trialitarian classes. -/
def pairwiseTarget (q : ThreeClasses β) : Target β where
  b23 := q.q2 + q.q3
  b12 := q.q1 + q.q2
  b13 := q.q1 + q.q3

/-- Add one common class to all three source entries.  In exponent two this is
precisely the diagonal symmetry of the pairwise target. -/
def diagonalTranslate (x : β) (q : ThreeClasses β) : ThreeClasses β where
  q1 := x + q.q1
  q2 := x + q.q2
  q3 := x + q.q3

/-- Every pairwise target satisfies the sum-zero central-character relation. -/
theorem pairwiseTarget_isAdmissible
    (twoTorsion : ∀ z : β, z + z = 0)
    (q : ThreeClasses β) :
    (pairwiseTarget q).IsAdmissible := by
  change (q.q2 + q.q3) + (q.q1 + q.q2) + (q.q1 + q.q3) = 0
  exact targetPairSums_sum_eq_zero
    twoTorsion q.q1 q.q2 q.q3

/-- Common diagonal translation does not change any pairwise target class. -/
theorem pairwiseTarget_diagonalTranslate
    (twoTorsion : ∀ z : β, z + z = 0)
    (x : β) (q : ThreeClasses β) :
    pairwiseTarget (diagonalTranslate x q) = pairwiseTarget q := by
  ext
  · change (x + q.q2) + (x + q.q3) = q.q2 + q.q3
    calc
      (x + q.q2) + (x + q.q3) = (x + x) + (q.q2 + q.q3) := by
        abel
      _ = q.q2 + q.q3 := by rw [twoTorsion x]; simp
  · change (x + q.q1) + (x + q.q2) = q.q1 + q.q2
    calc
      (x + q.q1) + (x + q.q2) = (x + x) + (q.q1 + q.q2) := by
        abel
      _ = q.q1 + q.q2 := by rw [twoTorsion x]; simp
  · change (x + q.q1) + (x + q.q3) = q.q1 + q.q3
    calc
      (x + q.q1) + (x + q.q3) = (x + x) + (q.q1 + q.q3) := by
        abel
      _ = q.q1 + q.q3 := by rw [twoTorsion x]; simp

/-- A canonical affine lift of an admissible target, with freely chosen first
source class `x`. -/
def liftTarget (t : Target β) (x : β) : ThreeClasses β where
  q1 := x
  q2 := x + t.b12
  q3 := x + t.b13

/-- Every admissible target is hit by each member of its canonical affine
family of lifts. -/
theorem pairwiseTarget_liftTarget
    (twoTorsion : ∀ z : β, z + z = 0)
    (t : Target β) (ht : t.IsAdmissible) (x : β) :
    pairwiseTarget (liftTarget t x) = t := by
  have h23 : t.b12 + t.b13 = t.b23 := by
    have hsum : t.b23 + (t.b12 + t.b13) = 0 := by
      simpa [Target.IsAdmissible, add_assoc] using ht
    simpa using (solve_second_of_add_eq twoTorsion hsum)
  ext
  · change (x + t.b12) + (x + t.b13) = t.b23
    calc
      (x + t.b12) + (x + t.b13) =
          (x + x) + (t.b12 + t.b13) := by abel
      _ = t.b12 + t.b13 := by rw [twoTorsion x]; simp
      _ = t.b23 := h23
  · change x + (x + t.b12) = t.b12
    calc
      x + (x + t.b12) = (x + x) + t.b12 := by abel
      _ = t.b12 := by rw [twoTorsion x]; simp
  · change x + (x + t.b13) = t.b13
    calc
      x + (x + t.b13) = (x + x) + t.b13 := by abel
      _ = t.b13 := by rw [twoTorsion x]; simp

/-- A source triple with target `t` is forced to be the canonical affine lift
with parameter equal to its first entry. -/
theorem eq_liftTarget_of_pairwiseTarget_eq
    (twoTorsion : ∀ z : β, z + z = 0)
    (q : ThreeClasses β) (t : Target β)
    (h : pairwiseTarget q = t) :
    q = liftTarget t q.q1 := by
  have h12 : q.q1 + q.q2 = t.b12 := by
    simpa [pairwiseTarget] using congrArg Target.b12 h
  have h13 : q.q1 + q.q3 = t.b13 := by
    simpa [pairwiseTarget] using congrArg Target.b13 h
  ext
  · rfl
  · simpa [liftTarget] using
      (solve_second_of_add_eq twoTorsion h12)
  · simpa [liftTarget] using
      (solve_second_of_add_eq twoTorsion h13)

/-- The image of the pairwise target map is exactly the admissible sum-zero
plane. -/
theorem exists_pairwiseTarget_eq_iff_isAdmissible
    (twoTorsion : ∀ z : β, z + z = 0)
    (t : Target β) :
    (∃ q : ThreeClasses β, pairwiseTarget q = t) ↔ t.IsAdmissible := by
  constructor
  · rintro ⟨q, rfl⟩
    exact pairwiseTarget_isAdmissible twoTorsion q
  · intro ht
    exact ⟨liftTarget t 0,
      pairwiseTarget_liftTarget twoTorsion t ht 0⟩

/-- Every fiber over an admissible target is canonically an affine copy of the
ambient exponent-two class group. -/
def pairwiseTargetFiberEquiv
    (twoTorsion : ∀ z : β, z + z = 0)
    (t : Target β) (ht : t.IsAdmissible) :
    β ≃ {q : ThreeClasses β // pairwiseTarget q = t} where
  toFun x := ⟨liftTarget t x,
    pairwiseTarget_liftTarget twoTorsion t ht x⟩
  invFun q := q.1.q1
  left_inv x := rfl
  right_inv q := by
    apply Subtype.ext
    exact (eq_liftTarget_of_pairwiseTarget_eq
      twoTorsion q.1 t q.2).symm

/-- Two source triples have the same pairwise target exactly when they differ
by one common diagonal translate. -/
theorem pairwiseTarget_eq_iff_exists_diagonalTranslate
    (twoTorsion : ∀ z : β, z + z = 0)
    (q q' : ThreeClasses β) :
    pairwiseTarget q' = pairwiseTarget q ↔
      ∃ x : β, q' = diagonalTranslate x q := by
  constructor
  · intro h
    have h12 : q'.q1 + q'.q2 = q.q1 + q.q2 := by
      simpa [pairwiseTarget] using congrArg Target.b12 h
    have h13 : q'.q1 + q'.q3 = q.q1 + q.q3 := by
      simpa [pairwiseTarget] using congrArg Target.b13 h
    refine ⟨q'.q1 + q.q1, ?_⟩
    ext
    · change q'.q1 = (q'.q1 + q.q1) + q.q1
      calc
        q'.q1 = q'.q1 + 0 := by simp
        _ = q'.q1 + (q.q1 + q.q1) := by rw [twoTorsion q.q1]; simp
        _ = (q'.q1 + q.q1) + q.q1 := by abel
    · change q'.q2 = (q'.q1 + q.q1) + q.q2
      calc
        q'.q2 = q'.q1 + (q.q1 + q.q2) :=
          solve_second_of_add_eq twoTorsion h12
        _ = (q'.q1 + q.q1) + q.q2 := by abel
    · change q'.q3 = (q'.q1 + q.q1) + q.q3
      calc
        q'.q3 = q'.q1 + (q.q1 + q.q3) :=
          solve_second_of_add_eq twoTorsion h13
        _ = (q'.q1 + q.q1) + q.q3 := by abel
  · rintro ⟨x, rfl⟩
    exact pairwiseTarget_diagonalTranslate twoTorsion x q

end RiemannResearch.E7.TrialityBrauerTarget
