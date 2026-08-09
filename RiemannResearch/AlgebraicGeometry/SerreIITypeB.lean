/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIITypeA

/-!
# Type-B form reduction for Serre II

This module refines the exact type-`B` neutrality provider by rank. A
`TypeBForm` records the rank `n ≥ 2` in `B_n`; the low-rank root system
`B₁` is handled by the `A₁` convention. No inner/outer split is needed
because the type-`B_n` Dynkin diagram has no nontrivial automorphism.

The declarations here are conditional assembly interfaces. They do not
construct root data, classify type-`B_n` groups as spin groups of
odd-dimensional quadratic forms, or prove their Serre-II neutrality.
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- The admissible rank of an irreducible Dynkin diagram of type `B_n`.
The convention `n ≥ 2` assigns the low-rank coincidence `B₁ = A₁` to
family `A`. -/
structure TypeBForm where
  rank : Nat
  rank_ge_two : 2 ≤ rank

/-- An abstract rank classifier for groups already classified as Dynkin
family `B`. Constructing it and proving its correctness are separate
algebraic-group obligations. -/
abbrev TypeBFormClassifier :=
  (R A : CommRingCat.{u}) → [HopfAlgebra R A] → TypeBForm

/-- A neutrality provider for type-`B_n` groups at one exact admissible
rank `n`. -/
abbrev TypeBRankNeutralityProvider
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeBForm : TypeBFormClassifier)
    (n : Nat) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    IsPerfectFieldCdAtMostTwo R →
    IsSemisimpleSimplyConnected R A →
    family R A = .B →
    (typeBForm R A).rank = n →
    Subsingleton (FpqcH1.{u, u} R A)

/-- Rank-indexed type-`B_n` providers for every `n ≥ 2` assemble into the
exact Dynkin-family-`B` provider. -/
theorem exactFamilyB_of_typeB_rank_providers
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeBForm : TypeBFormClassifier)
    (rankB : ∀ n, 2 ≤ n →
      TypeBRankNeutralityProvider IsPerfectFieldCdAtMostTwo
        IsSemisimpleSimplyConnected family typeBForm n) :
    ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .B := by
  intro R A _ hField hGroup hB
  exact rankB (typeBForm R A).rank (typeBForm R A).rank_ge_two
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
    (rankB : ∀ n, 2 ≤ n →
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
      (NonE8GroupCondition IsSemisimpleSimplyConnected family) := by
  let a :=
    exactFamilyA_of_typeA_form_providers IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family typeAForm innerA outerA
  let b :=
    exactFamilyB_of_typeB_rank_providers IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family typeBForm rankB
  rw [conjecture_iff_subsingleton]
  intro R A _ hField hGroup
  rcases hGroup with ⟨hSemisimpleSimplyConnected, hne⟩
  generalize hfamily : family R A = dynkin at hne
  cases dynkin with
  | A => exact a R A hField hSemisimpleSimplyConnected hfamily
  | B => exact b R A hField hSemisimpleSimplyConnected hfamily
  | C => exact c R A hField hSemisimpleSimplyConnected hfamily
  | D => exact d R A hField hSemisimpleSimplyConnected hfamily
  | E6 => exact e6 R A hField hSemisimpleSimplyConnected hfamily
  | E7 => exact e7 R A hField hSemisimpleSimplyConnected hfamily
  | E8 => exact (hne rfl).elim
  | F4 => exact f4 R A hField hSemisimpleSimplyConnected hfamily
  | G2 => exact g2 R A hField hSemisimpleSimplyConnected hfamily

end RiemannResearch.AlgebraicGeometry.SerreII
