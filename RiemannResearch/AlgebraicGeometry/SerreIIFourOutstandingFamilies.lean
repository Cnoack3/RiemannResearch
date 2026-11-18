/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIINonE8

/-!
# The four outstanding Dynkin-family providers for Serre II

Relative to supplied exact providers for the settled families `A`, `B`, `C`,
`F4`, and `G2`, the remaining family-level boundary in the current Serre-II
architecture consists of exactly four providers:

* type `D` (including trialitarian `D4`),
* type `E6`,
* type `E7`, and
* type `E8`.

This module packages those four endpoints and proves that, once the five other
family providers are fixed, their conjunction is exactly equivalent to the
supplied full Serre-II `Conjecture` target.

The declarations here are logical assembly only.  They do not prove any of the
four providers, construct the Dynkin-family classifier, or formalize the
semisimple factor decomposition needed to connect the one-family classifier
to every semisimple simply connected group.
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- The four exact family-neutrality providers left open by the present
family-level reduction.  The fields are endpoints to be supplied by the
genuine `D4`, `E6`, `E7`, and `E8` bridge theorems; the structure does not
identify those mathematical bridge statements with their endpoints. -/
structure FourOutstandingFamilyNeutralityProviders
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier) : Prop where
  d : ExactFamilyNeutralityProvider Base Group family .D
  e6 : ExactFamilyNeutralityProvider Base Group family .E6
  e7 : ExactFamilyNeutralityProvider Base Group family .E7
  e8 : ExactFamilyNeutralityProvider Base Group family .E8

/-- The five supplied settled-family providers and the four outstanding
providers assemble to the full one-family-classifier Serre-II target. -/
theorem conjecture_of_four_outstanding_family_providers
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (a : ExactFamilyNeutralityProvider Base Group family .A)
    (b : ExactFamilyNeutralityProvider Base Group family .B)
    (c : ExactFamilyNeutralityProvider Base Group family .C)
    (f4 : ExactFamilyNeutralityProvider Base Group family .F4)
    (g2 : ExactFamilyNeutralityProvider Base Group family .G2)
    (outstanding :
      FourOutstandingFamilyNeutralityProviders Base Group family) :
    Conjecture Base Group :=
  conjecture_of_exact_family_providers Base Group family
    a b c outstanding.d outstanding.e6 outstanding.e7 outstanding.e8 f4 g2

/-- Any proof of the supplied full conjecture restricts to the four outstanding
exact-family providers. -/
theorem four_outstanding_family_providers_of_conjecture
    {Base : BaseCondition}
    {Group : GroupCondition}
    {family : DynkinFamilyClassifier}
    (h : Conjecture Base Group) :
    FourOutstandingFamilyNeutralityProviders Base Group family := by
  rw [conjecture_iff_subsingleton] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K A _ _ _ hBase hGroup _
    exact h K A hBase hGroup
  · intro K A _ _ _ hBase hGroup _
    exact h K A hBase hGroup
  · intro K A _ _ _ hBase hGroup _
    exact h K A hBase hGroup
  · intro K A _ _ _ hBase hGroup _
    exact h K A hBase hGroup

/-- Once exact providers for `A`, `B`, `C`, `F4`, and `G2` are fixed, the
supplied full Serre-II target is equivalent to the conjunction of the four
outstanding type-`D`, `E6`, `E7`, and `E8` providers. -/
theorem conjecture_iff_four_outstanding_family_providers
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (a : ExactFamilyNeutralityProvider Base Group family .A)
    (b : ExactFamilyNeutralityProvider Base Group family .B)
    (c : ExactFamilyNeutralityProvider Base Group family .C)
    (f4 : ExactFamilyNeutralityProvider Base Group family .F4)
    (g2 : ExactFamilyNeutralityProvider Base Group family .G2) :
    Conjecture Base Group ↔
      FourOutstandingFamilyNeutralityProviders Base Group family :=
  ⟨four_outstanding_family_providers_of_conjecture,
    conjecture_of_four_outstanding_family_providers
      Base Group family a b c f4 g2⟩

end RiemannResearch.AlgebraicGeometry.SerreII
