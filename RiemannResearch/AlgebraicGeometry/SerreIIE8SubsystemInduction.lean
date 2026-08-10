/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIIConjecture

/-!
# Excluding induction from proper maximal-rank E8 subsystems

This module isolates the pointed-set argument that a nonneutral E8 class
cannot be induced from any of the six proper maximal-rank subsystem families

`half-spin D8`, `A8`, `E7 A1`, `E6 A2`, `A4 A4`, and `G2 F4`,

provided that every source subsystem satisfies Serre II and that induction
preserves the neutral class.

The six source `H¹` types and their induction maps are abstract because the
corresponding central quotients, group-scheme embeddings, and functorial maps
on the project's fpqc `H¹` have not yet been constructed. In particular,
`half-spin D8` and several product-type embedded subgroups should not be
silently identified with their simply connected covers.

Source: user-provided argument.
-/

universe u x

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- The six proper maximal-rank subsystem families in the E8 induction
exclusion argument. -/
inductive E8SubsystemFamily
  | halfSpinD8
  | A8
  | E7A1
  | E6A2
  | A4A4
  | G2F4
  deriving DecidableEq

/-- Pointed `H¹` induction data from the six proper maximal-rank subsystem
families into one target pointed set.

For an eventual algebraic-group instantiation, `H1 s` is the source
cohomology set, `induce s` is induced by the subsystem embedding into E8, and
`induce_neutral` is functoriality at the distinguished class. -/
structure E8SubsystemInduction {X : Type x} (neutral : X) where
  H1 : E8SubsystemFamily → Type u
  sourceNeutral : ∀ s, H1 s
  induce : ∀ s, H1 s → X
  induce_neutral : ∀ s, induce s (sourceNeutral s) = neutral

namespace E8SubsystemInduction

/-- Serre II for all six subsystem sources, expressed by saying that each
source `H¹` is a subsingleton. -/
abbrev AllSubsystemsSerreII {X : Type x} {neutral : X}
    (D : E8SubsystemInduction.{u, x} neutral) : Prop :=
  ∀ s, Subsingleton (D.H1 s)

/-- The six separate subsystem Serre-II conclusions assemble into the
family-level provider. -/
theorem allSubsystemsSerreII_of_family_providers
    {X : Type x} {neutral : X}
    (D : E8SubsystemInduction.{u, x} neutral)
    (halfSpinD8 : Subsingleton (D.H1 .halfSpinD8))
    (a8 : Subsingleton (D.H1 .A8))
    (e7a1 : Subsingleton (D.H1 .E7A1))
    (e6a2 : Subsingleton (D.H1 .E6A2))
    (a4a4 : Subsingleton (D.H1 .A4A4))
    (g2f4 : Subsingleton (D.H1 .G2F4)) :
    D.AllSubsystemsSerreII := by
  intro s
  cases s <;> assumption

/-- If the source subsystem satisfies Serre II, every class induced from it
is neutral. -/
theorem induced_eq_neutral
    {X : Type x} {neutral : X}
    (D : E8SubsystemInduction.{u, x} neutral)
    (hSerreII : D.AllSubsystemsSerreII)
    (s : E8SubsystemFamily) (η : D.H1 s) :
    D.induce s η = neutral := by
  rw [(hSerreII s).allEq η (D.sourceNeutral s)]
  exact D.induce_neutral s

/-- Under Serre II for the source subsystem, a target class is induced from
that subsystem exactly when it is neutral. -/
theorem exists_induced_iff_eq_neutral
    {X : Type x} {neutral : X}
    (D : E8SubsystemInduction.{u, x} neutral)
    (hSerreII : D.AllSubsystemsSerreII)
    (s : E8SubsystemFamily) (ξ : X) :
    (∃ η : D.H1 s, D.induce s η = ξ) ↔ ξ = neutral := by
  constructor
  · rintro ⟨η, rfl⟩
    exact D.induced_eq_neutral hSerreII s η
  · intro hξ
    refine ⟨D.sourceNeutral s, ?_⟩
    exact (D.induce_neutral s).trans hξ.symm

/-- A nonneutral target class cannot be induced from any of the six proper
maximal-rank subsystem families. -/
theorem nonneutral_not_induced
    {X : Type x} {neutral : X}
    (D : E8SubsystemInduction.{u, x} neutral)
    (hSerreII : D.AllSubsystemsSerreII)
    {ξ : X} (hξ : ξ ≠ neutral) :
    ¬ ∃ s, ∃ η : D.H1 s, D.induce s η = ξ := by
  rintro ⟨s, η, rfl⟩
  exact hξ (D.induced_eq_neutral hSerreII s η)

/-- Explicit six-provider form: if half-spin D8, A8, E7 A1, E6 A2, A4 A4,
and G2 F4 all satisfy Serre II, no nonneutral target class is induced from
any of them. -/
theorem nonneutral_not_induced_from_six_serreII_subsystems
    {X : Type x} {neutral : X}
    (D : E8SubsystemInduction.{u, x} neutral)
    (halfSpinD8 : Subsingleton (D.H1 .halfSpinD8))
    (a8 : Subsingleton (D.H1 .A8))
    (e7a1 : Subsingleton (D.H1 .E7A1))
    (e6a2 : Subsingleton (D.H1 .E6A2))
    (a4a4 : Subsingleton (D.H1 .A4A4))
    (g2f4 : Subsingleton (D.H1 .G2F4))
    {ξ : X} (hξ : ξ ≠ neutral) :
    ¬ ∃ s, ∃ η : D.H1 s, D.induce s η = ξ :=
  D.nonneutral_not_induced
    (D.allSubsystemsSerreII_of_family_providers
      halfSpinD8 a8 e7a1 e6a2 a4a4 g2f4)
    hξ

end E8SubsystemInduction

end RiemannResearch.AlgebraicGeometry.SerreII
