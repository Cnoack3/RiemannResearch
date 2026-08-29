/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.ThreeQuaternionBrauerCompletion

/-!
# The degree-four unitary-discriminant boundary in the E7 problem

For the three-quaternion target, put

```
a = q2 + q3
c = q1 + q2.
```

The desired Clifford invariant is the class of `c` modulo the subgroup
spanned by `a`.  In an exponent-two Brauer group, the two representatives of
that coset are

```
c = q1 + q2,
c + a = q1 + q3.
```

Bingöl--Quéguiner-Mathieu, Proposition 3.5 and Lemma 3.7, show that a
quadratic extension of a degree-four algebra with unitary involution produces
a degree-eight quadratic pair whose Clifford invariant is represented by the
discriminant algebra of the unitary involution.  By KMRT, Proposition 10.30,
the discriminant algebra of a degree-four unitary algebra has index `1` or
`2`.  Consequently this construction mechanism can reach the target Clifford
coset only if at least one of `q1 + q2` and `q1 + q3` has index at most `2`.

This module formalizes precisely the exponent-two additive implication.  The
predicate `Small` abstracts "represented by an algebra of index at most 2".
No central simple algebras, involutions, discriminant algebras, or quadratic
pairs are constructed here.  The external algebraic theorems are therefore
not hidden as Lean axioms: their exact additive consequence is exposed as a
certificate interface.

References:

* F. K. Bingöl and A. Quéguiner-Mathieu, *Triality over fields with
  `I^3 = 0`*, Proposition 3.5 and Lemma 3.7, arXiv:2312.10442v2.
* M.-A. Knus, A. Merkurjev, M. Rost, and J.-P. Tignol, *The Book of
  Involutions*, Proposition 10.30.
-/

namespace RiemannResearch.E7.ThreeQuaternionUnitaryDiscriminantObstruction

open RiemannResearch.E7.ThreeQuaternionBrauerCompletion

variable {β : Type*} [AddCommGroup β]

/-- A class `representative` represents the coset of `target` modulo the
order-two class `underlying` when it is either `target` or
`target + underlying`. -/
def RepresentsOrderTwoCoset
    (underlying target representative : β) : Prop :=
  representative = target ∨ representative = target + underlying

/-- Abstract certificate supplied by the degree-four unitary-discriminant
route.  In the intended application, `Small` means Schur index at most `2`,
and `discriminantClass` is the class of the discriminant algebra. -/
structure DegreeFourUnitaryDiscriminantCertificate
    (Small : β → Prop) (q1 q2 q3 : β) where
  discriminantClass : β
  small_discriminant : Small discriminantClass
  represents_target_clifford_coset :
    RepresentsOrderTwoCoset
      (q2 + q3) (q1 + q2) discriminantClass

/-- The second representative of the target Clifford coset is `q1 + q3`. -/
theorem target_plus_underlying_eq_other
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 : β) :
    (q1 + q2) + (q2 + q3) = q1 + q3 := by
  calc
    (q1 + q2) + (q2 + q3) = q1 + (q2 + q2) + q3 := by abel
    _ = q1 + q3 := by rw [twoTorsion q2]; simp

/-- Adding the underlying class again swaps the other representative back to
the selected representative. -/
theorem other_plus_underlying_eq_target
    (twoTorsion : ∀ z : β, z + z = 0)
    (q1 q2 q3 : β) :
    (q1 + q3) + (q2 + q3) = q1 + q2 := by
  calc
    (q1 + q3) + (q2 + q3) = q1 + q2 + (q3 + q3) := by abel
    _ = q1 + q2 := by rw [twoTorsion q3]; simp

/-- The abstract degree-four unitary certificate exists exactly when one of
the two target Clifford representatives satisfies `Small`. -/
theorem nonempty_degreeFourUnitaryDiscriminantCertificate_iff
    (twoTorsion : ∀ z : β, z + z = 0)
    (Small : β → Prop)
    (q1 q2 q3 : β) :
    Nonempty
        (DegreeFourUnitaryDiscriminantCertificate Small q1 q2 q3) ↔
      Small (q1 + q2) ∨ Small (q1 + q3) := by
  constructor
  · rintro ⟨certificate⟩
    rcases certificate.represents_target_clifford_coset with h | h
    · left
      simpa [h] using certificate.small_discriminant
    · right
      have hsmall := certificate.small_discriminant
      rw [h, target_plus_underlying_eq_other
        twoTorsion q1 q2 q3] at hsmall
      exact hsmall
  · intro h
    rcases h with h12 | h13
    · exact ⟨{
        discriminantClass := q1 + q2
        small_discriminant := h12
        represents_target_clifford_coset := Or.inl rfl
      }⟩
    · exact ⟨{
        discriminantClass := q1 + q3
        small_discriminant := h13
        represents_target_clifford_coset := Or.inr
          (target_plus_underlying_eq_other
            twoTorsion q1 q2 q3).symm
      }⟩

/-- The hard three-quaternion stratum: none of the three trialitarian pair
sums satisfies the supplied low-index predicate. -/
def HardPairSumStratum
    (Small : β → Prop) (q1 q2 q3 : β) : Prop :=
  ¬ Small (q1 + q2) ∧
  ¬ Small (q1 + q3) ∧
  ¬ Small (q2 + q3)

/-- The hard stratum is stable under the cyclic permutation
`(q1,q2,q3) ↦ (q2,q3,q1)`. -/
theorem hardPairSumStratum_rotate
    (Small : β → Prop) {q1 q2 q3 : β}
    (h : HardPairSumStratum Small q1 q2 q3) :
    HardPairSumStratum Small q2 q3 q1 := by
  rcases h with ⟨h12, h13, h23⟩
  refine ⟨h23, ?_, ?_⟩
  · simpa [add_comm] using h12
  · simpa [add_comm] using h13

/-- The hard stratum is stable under the transposition of `q2` and `q3`. -/
theorem hardPairSumStratum_swap23
    (Small : β → Prop) {q1 q2 q3 : β}
    (h : HardPairSumStratum Small q1 q2 q3) :
    HardPairSumStratum Small q1 q3 q2 := by
  rcases h with ⟨h12, h13, h23⟩
  refine ⟨h13, h12, ?_⟩
  simpa [add_comm] using h23

/-- A degree-four unitary discriminant certificate is impossible in the hard
pair-sum stratum. -/
theorem no_degreeFourUnitaryDiscriminantCertificate_of_hardPairSumStratum
    (twoTorsion : ∀ z : β, z + z = 0)
    (Small : β → Prop) {q1 q2 q3 : β}
    (hHard : HardPairSumStratum Small q1 q2 q3) :
    ¬ Nonempty
        (DegreeFourUnitaryDiscriminantCertificate Small q1 q2 q3) := by
  intro hCertificate
  have hSmall : Small (q1 + q2) ∨ Small (q1 + q3) :=
    (nonempty_degreeFourUnitaryDiscriminantCertificate_iff
      twoTorsion Small q1 q2 q3).mp hCertificate
  rcases hHard with ⟨h12, h13, _⟩
  rcases hSmall with h12' | h13'
  · exact h12 h12'
  · exact h13 h13'

/-- The zero-parameter four-quaternion shortcut from the affine-completion
module is also unavailable in the hard pair-sum stratum.  This does not rule
out a completion with a nonzero affine parameter. -/
theorem no_zeroAffineQuaternionCompletion_of_hardPairSumStratum
    (IsQuaternion : β → Prop) {q1 q2 q3 : β}
    (hHard : HardPairSumStratum IsQuaternion q1 q2 q3) :
    ¬ IsAffineQuaternionCompletion IsQuaternion q1 q2 q3 0 := by
  intro hCompletion
  rcases hHard with ⟨_, _, h23⟩
  rcases hCompletion with ⟨_, h23', _, _⟩
  apply h23
  simpa using h23'

end RiemannResearch.E7.ThreeQuaternionUnitaryDiscriminantObstruction
