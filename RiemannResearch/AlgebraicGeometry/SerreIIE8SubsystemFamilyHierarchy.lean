/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIIFamilyHierarchy
import RiemannResearch.AlgebraicGeometry.SerreIIE8SubsystemInduction

/-!
# Shared family providers in the E8 subsystem reduction

This module is the adapter between the generic pointed-set subsystem-induction
argument and the shared non-`E8` Dynkin-family hierarchy. It records which
proper family providers each maximal-rank subsystem uses and keeps the passage
to the actual source `H¹` as an explicit bridge.

The bridge is load-bearing: component neutrality does not automatically pass
through products, half-spin groups, or central quotients. This module also
shares only family-level neutrality conclusions. It does not yet share the
lower-level `D4` triality constructions that future type-`D` and `E8`
developments should import from a common foundation.

Source: user-provided architectural decision and subsystem-induction argument
(14 August 2026).
-/

universe u x

namespace RiemannResearch.AlgebraicGeometry.SerreII

namespace E8SubsystemFamily

/-- The proper irreducible Dynkin families whose neutrality results are used
by each maximal-rank `E8` subsystem source.

Ranks and form kinds are intentionally erased because an exact family provider
is uniform over them. The repeated `A4` factor in `A4 A4` is listed once
because the same family provider is reused; multiplicity and product
cohomology remain obligations of `E8SubsystemSourceNeutralityBridge`. -/
def RequiresFamily : E8SubsystemFamily → DynkinFamily → Prop
  | .halfSpinD8, d => d = .D
  | .A8, d => d = .A
  | .E7A1, d => d = .E7 ∨ d = .A
  | .E6A2, d => d = .E6 ∨ d = .A
  | .A4A4, d => d = .A
  | .G2F4, d => d = .G2 ∨ d = .F4

/-- Every component family required by a proper maximal-rank `E8`
subsystem is non-`E8`. -/
theorem RequiresFamily.ne_e8
    {s : E8SubsystemFamily} {d : DynkinFamily}
    (h : RequiresFamily s d) : d ≠ .E8 := by
  cases s <;> simp [RequiresFamily] at h ⊢ <;> aesop

end E8SubsystemFamily

/-- The explicit bridge from neutrality of all jointly required irreducible
families to neutrality of an actual maximal-rank subsystem source `H¹`.

Constructing this structure is an open research obligation. An eventual
instantiation must supply the necessary product-`H¹`, central-isogeny, and
cohomological lifting results; the component family providers alone do not
construct it. -/
structure E8SubsystemSourceNeutralityBridge
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    {X : Type x} {neutral : X}
    (D : E8SubsystemInduction.{u, x} neutral) : Prop where
  source_of_required_families :
    ∀ s,
      (∀ d, E8SubsystemFamily.RequiresFamily s d →
        ExactFamilyNeutralityProvider Base Group family d) →
      Subsingleton (D.H1 s)

namespace E8SubsystemInduction

/-- The shared non-`E8` family hierarchy neutralizes all six proper
subsystem sources once the explicit source-`H¹` bridge has been supplied. -/
theorem allSubsystemsSerreII_of_hierarchy
    {Base : BaseCondition}
    {Group : GroupCondition}
    {family : DynkinFamilyClassifier}
    {X : Type x} {neutral : X}
    (D : E8SubsystemInduction.{u, x} neutral)
    (H : NonE8FamilyNeutralityHierarchy Base Group family)
    (bridge : E8SubsystemSourceNeutralityBridge Base Group family D) :
    D.AllSubsystemsSerreII := by
  intro s
  exact bridge.source_of_required_families s fun d hd =>
    H.provider d hd.ne_e8

/-- A nonneutral target class is excluded from every proper subsystem image
using the shared proper-family hierarchy and the explicit source-`H¹`
bridge. -/
theorem nonneutral_not_induced_of_hierarchy
    {Base : BaseCondition}
    {Group : GroupCondition}
    {family : DynkinFamilyClassifier}
    {X : Type x} {neutral : X}
    (D : E8SubsystemInduction.{u, x} neutral)
    (H : NonE8FamilyNeutralityHierarchy Base Group family)
    (bridge : E8SubsystemSourceNeutralityBridge Base Group family D)
    {ξ : X} (hξ : ξ ≠ neutral) :
    ¬ ∃ s, ∃ η : D.H1 s, D.induce s η = ξ :=
  D.nonneutral_not_induced (D.allSubsystemsSerreII_of_hierarchy H bridge) hξ

end E8SubsystemInduction

end RiemannResearch.AlgebraicGeometry.SerreII
