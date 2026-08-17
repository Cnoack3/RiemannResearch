/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIINonE8

/-!
# Shared Dynkin-family hierarchy for Serre II

This module packages all proper non-`E8` family providers behind one indexed
interface. Family-specific developments produce exact providers and enter the
hierarchy through `of_exact_providers`; non-`E8` assembly and the final
`E8` branch then consume the same hierarchy.

This first hierarchy shares neutrality conclusions, not the internal
root-data, Spin, or triality constructions used to prove them. A future
lower-level triality module can be imported by both the type-`D` and `E8`
developments without changing this provider interface.

The hierarchy records reusable proof material, not implications between
different Dynkin types. In particular, a type-`D` provider does not by itself
prove anything about an `E8` torsor. The separate subsystem bridge in
`SerreIIE8SubsystemFamilyHierarchy` records the load-bearing passage from
component-family neutrality to the actual central-quotient subsystem `H¹`.

Source: user-provided architectural decision (14 August 2026).
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- Exact neutrality providers for every irreducible Dynkin family proper
relative to `E8`.

The indexed field is the shared interface consumed by both the broad
non-`E8` theorem and the proper-subsystem part of the `E8` program. -/
structure NonE8FamilyNeutralityHierarchy
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier) : Prop where
  provider :
    ∀ d, d ≠ .E8 →
      ExactFamilyNeutralityProvider Base Group family d

namespace NonE8FamilyNeutralityHierarchy

/-- The eight exact proper-family providers assemble into the indexed shared
hierarchy. -/
theorem of_exact_providers
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (a : ExactFamilyNeutralityProvider Base Group family .A)
    (b : ExactFamilyNeutralityProvider Base Group family .B)
    (c : ExactFamilyNeutralityProvider Base Group family .C)
    (d : ExactFamilyNeutralityProvider Base Group family .D)
    (e6 : ExactFamilyNeutralityProvider Base Group family .E6)
    (e7 : ExactFamilyNeutralityProvider Base Group family .E7)
    (f4 : ExactFamilyNeutralityProvider Base Group family .F4)
    (g2 : ExactFamilyNeutralityProvider Base Group family .G2) :
    NonE8FamilyNeutralityHierarchy Base Group family := by
  refine ⟨?_⟩
  intro e hne
  cases e with
  | A => exact a
  | B => exact b
  | C => exact c
  | D => exact d
  | E6 => exact e6
  | E7 => exact e7
  | E8 => exact (hne rfl).elim
  | F4 => exact f4
  | G2 => exact g2

/-- The shared proper-family hierarchy supplies the non-`E8` Serre-II
conjecture. -/
theorem conjecture_nonE8
    {Base : BaseCondition}
    {Group : GroupCondition}
    {family : DynkinFamilyClassifier}
    (H : NonE8FamilyNeutralityHierarchy Base Group family) :
    H1Conjecture Base (NonE8GroupCondition Group family) :=
  conjecture_nonE8_of_exact_family_providers Base Group family
    (H.provider .A (by decide))
    (H.provider .B (by decide))
    (H.provider .C (by decide))
    (H.provider .D (by decide))
    (H.provider .E6 (by decide))
    (H.provider .E7 (by decide))
    (H.provider .F4 (by decide))
    (H.provider .G2 (by decide))

/-- A proof of the non-`E8` conjecture recovers the indexed proper-family
hierarchy. This direction exposes the exact family provider needed by later
consumers without strengthening the conjecture. -/
theorem of_conjecture_nonE8
    {Base : BaseCondition}
    {Group : GroupCondition}
    {family : DynkinFamilyClassifier}
    (h : H1Conjecture Base (NonE8GroupCondition Group family)) :
    NonE8FamilyNeutralityHierarchy Base Group family := by
  rw [h1Conjecture_iff_subsingleton] at h
  refine ⟨?_⟩
  intro d hd R A _ hBase hGroup hfamily
  exact h R A hBase ⟨hGroup, hfamily.trans_ne hd⟩

/-- The indexed proper-family hierarchy is exactly equivalent to the existing
non-`E8` conjecture interface. -/
theorem conjecture_nonE8_iff_hierarchy
    {Base : BaseCondition}
    {Group : GroupCondition}
    {family : DynkinFamilyClassifier} :
    H1Conjecture Base (NonE8GroupCondition Group family) ↔
      NonE8FamilyNeutralityHierarchy Base Group family :=
  ⟨of_conjecture_nonE8, conjecture_nonE8⟩

/-- Adding one exact `E8` provider to the shared proper-family hierarchy
supplies the full one-family-classifier H1 target. -/
theorem conjecture_of_e8
    {Base : BaseCondition}
    {Group : GroupCondition}
    {family : DynkinFamilyClassifier}
    (H : NonE8FamilyNeutralityHierarchy Base Group family)
    (e8 : ExactFamilyNeutralityProvider Base Group family .E8) :
    H1Conjecture Base Group :=
  conjecture_of_nonE8_and_e8 Base Group family H.conjecture_nonE8 e8

end NonE8FamilyNeutralityHierarchy

end RiemannResearch.AlgebraicGeometry.SerreII
