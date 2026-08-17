/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIITypeA

/-!
# Type-B form reduction for Serre II

This module refines the exact type-`B` neutrality provider by rank. A
`TypeBForm` records every positive rank `n` in `B_n`, including `B₁`.
No identification of `B₁` with `A₁` is assumed. Any comparison between
those low-rank classifications requires a separate theorem about the supplied
root data or algebraic groups.

The declarations here are conditional assembly interfaces. They do not
construct root data, classify type-`B_n` groups as spin groups of
odd-dimensional quadratic forms, or prove their Serre-II neutrality.
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- The positive rank of a type-`B_n` form. In particular, rank one remains
an explicit type-`B` case in this interface. -/
structure TypeBForm where
  rank : Nat
  rank_pos : 0 < rank

/-- An abstract rank classifier for groups already classified as Dynkin
family `B`. Constructing it and proving its correctness are separate
algebraic-group obligations. -/
abbrev TypeBFormClassifier :=
  (R A : Type u) → [Field R] → [CommRing A] → [HopfAlgebra R A] → TypeBForm

/-- A neutrality provider for type-`B_n` groups at one exact admissible
rank `n`. -/
abbrev TypeBRankNeutralityProvider
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeBForm : TypeBFormClassifier)
    (n : Nat) : Prop :=
  ∀ (R A : Type u) [Field R] [CommRing A] [HopfAlgebra R A],
    IsPerfectFieldCdAtMostTwo R →
    IsSemisimpleSimplyConnected R A →
    family R A = .B →
    (typeBForm R A).rank = n →
    Subsingleton (GaloisH1 R A)

/-- Rank-indexed type-`B_n` providers for every positive `n` assemble into the
exact Dynkin-family-`B` provider. -/
theorem exactFamilyB_of_typeB_rank_providers
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeBForm : TypeBFormClassifier)
    (rankB : ∀ n, 0 < n →
      TypeBRankNeutralityProvider IsPerfectFieldCdAtMostTwo
        IsSemisimpleSimplyConnected family typeBForm n) :
    ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .B := by
  intro R A _ _ _ hField hGroup hB
  exact rankB (typeBForm R A).rank (typeBForm R A).rank_pos
    R A hField hGroup hB rfl

/-- The non-`E8` reduction with type `A_n` split into inner and outer
providers, type `B_n` split by admissible rank, and the remaining classical
series exposed individually. -/
theorem conjecture_nonE8_of_typeA_and_typeB_form_providers
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeAForm : TypeAFormClassifier)
    (innerA : TypeAFormNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family typeAForm TypeAForm.IsInner)
    (outerA : TypeAFormNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family typeAForm TypeAForm.IsOuter)
    (typeBForm : TypeBFormClassifier)
    (rankB : ∀ n, 0 < n →
      TypeBRankNeutralityProvider IsPerfectFieldCdAtMostTwo
        IsSemisimpleSimplyConnected family typeBForm n)
    (c : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .C)
    (d : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .D)
    (e6 : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .E6)
    (e7 : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .E7)
    (f4 : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .F4)
    (g2 : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .G2) :
    Conjecture IsPerfectFieldCdAtMostTwo
      (NonE8GroupCondition IsSemisimpleSimplyConnected family) :=
  conjecture_nonE8_of_typeA_form_providers IsPerfectFieldCdAtMostTwo
    IsSemisimpleSimplyConnected family typeAForm innerA outerA
    (exactFamilyB_of_typeB_rank_providers IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family typeBForm rankB)
    c d e6 e7 f4 g2

end RiemannResearch.AlgebraicGeometry.SerreII
