/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIIFamilyHierarchy

/-!
# Type-A form reduction for Serre II

This module refines the exact type-`A` neutrality provider into inner and
outer form providers. A `TypeAForm` records the rank `n` in `A_n` and
whether the form is inner or outer. The outer constructor is restricted to
rank at least two, reflecting that the Dynkin diagram of `A₁` has no
nontrivial diagram automorphism.

The declarations here are conditional assembly interfaces. They do not
construct root data, classify algebraic groups of type `A_n`, identify inner
forms with special linear groups of central simple algebras, identify outer
forms with unitary groups, or prove their Serre-II neutrality.
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- Inner versus outer forms of an irreducible Dynkin diagram of type `A_n`. -/
inductive TypeAFormKind
  | inner
  | outer
  deriving DecidableEq

/-- The rank and inner/outer kind of a type-`A_n` form.

The rank is positive. An outer form must have rank at least two because
`A₁` has no nontrivial diagram automorphism. -/
structure TypeAForm where
  rank : Nat
  rank_pos : 0 < rank
  kind : TypeAFormKind
  outer_rank : kind = .outer → 2 ≤ rank

namespace TypeAForm

/-- Select the inner type-`A_n` forms, for every positive rank `n`. -/
def IsInner (form : TypeAForm) : Prop := form.kind = .inner

/-- Select the outer type-`A_n` forms, necessarily with `n ≥ 2`. -/
def IsOuter (form : TypeAForm) : Prop := form.kind = .outer

theorem inner_or_outer (form : TypeAForm) :
    form.IsInner ∨ form.IsOuter := by
  rcases form with ⟨rank, rank_pos, kind, outer_rank⟩
  cases kind <;> simp [IsInner, IsOuter]

end TypeAForm

/-- An abstract rank-and-form classifier for groups already classified as
Dynkin family `A`. Constructing it and proving its correctness are separate
algebraic-group obligations. -/
abbrev TypeAFormClassifier :=
  (R A : CommRingCat.{u}) → [HopfAlgebra R A] → TypeAForm

/-- A neutrality provider for selected type-`A_n` forms.

The explicit `family R A = .A` hypothesis prevents the auxiliary
`typeAForm` classifier from extending the type-`A` scope by itself. -/
abbrev TypeAFormNeutralityProvider
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeAForm : TypeAFormClassifier)
    (Select : TypeAForm → Prop) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    IsPerfectFieldCdAtMostTwo R →
    IsSemisimpleSimplyConnected R A →
    family R A = .A →
    Select (typeAForm R A) →
    Subsingleton (FpqcH1.{u, u} R A)

/-- Inner and outer type-`A_n` neutrality providers, covering all admissible
ranks, assemble into the exact Dynkin-family-`A` provider. -/
theorem exactFamilyA_of_typeA_form_providers
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeAForm : TypeAFormClassifier)
    (inner : TypeAFormNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family typeAForm TypeAForm.IsInner)
    (outer : TypeAFormNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family typeAForm TypeAForm.IsOuter) :
    ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .A := by
  intro R A _ hField hGroup hA
  rcases TypeAForm.inner_or_outer (typeAForm R A) with hInner | hOuter
  · exact inner R A hField hGroup hA hInner
  · exact outer R A hField hGroup hA hOuter

/-- The non-`E8` reduction with type `A_n` exposed as separate inner and
outer form providers and the other classical series exposed individually. -/
theorem conjecture_nonE8_of_typeA_form_providers
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeAForm : TypeAFormClassifier)
    (innerA : TypeAFormNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family typeAForm TypeAForm.IsInner)
    (outerA : TypeAFormNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family typeAForm TypeAForm.IsOuter)
    (b : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .B)
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
    H1Conjecture IsPerfectFieldCdAtMostTwo
      (NonE8GroupCondition IsSemisimpleSimplyConnected family) :=
  conjecture_nonE8_of_exact_family_providers IsPerfectFieldCdAtMostTwo
    IsSemisimpleSimplyConnected family
    (exactFamilyA_of_typeA_form_providers IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family typeAForm innerA outerA)
    b c d e6 e7 f4 g2

end RiemannResearch.AlgebraicGeometry.SerreII
