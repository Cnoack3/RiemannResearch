/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIIConjecture

/-!
# The non-E8 Dynkin-family reduction for Serre II

This module gives a finite, fpqc-level assembly theorem: once a supplied
Dynkin-family classifier and neutrality providers cover the classical series,
`E6`, `E7`, `F4`, and `G2`, the project's auxiliary H1 target follows for
the corresponding non-`E8` scope. It also records the final abstract bridge
from that non-`E8` result and an exact `E8` provider to the full supplied
group condition.

This does not construct a Dynkin classifier or prove the family providers.
In particular, for arbitrary forms the trialitarian `D4`, `E6`, and `E7`
inputs contain presently open mathematics. For quasi-split groups these
non-`E8` cases are known in the literature, but their algebraic-group and
fpqc-cohomology formalization is not yet present in this project.
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- The irreducible Dynkin families. The classical constructors denote the
full series `Aₙ`, `Bₙ`, `Cₙ`, and `Dₙ`. -/
inductive DynkinFamily
  | A
  | B
  | C
  | D
  | E6
  | E7
  | E8
  | F4
  | G2
  deriving DecidableEq

namespace DynkinFamily

/-- The four classical Dynkin series. -/
def IsClassical : DynkinFamily → Prop
  | .A | .B | .C | .D => True
  | _ => False

/-- All five exceptional Dynkin types, including `E8`. -/
def IsExceptional : DynkinFamily → Prop
  | .E6 | .E7 | .E8 | .F4 | .G2 => True
  | _ => False

/-- Exactly the exceptional Dynkin types left after excluding `E8`. -/
def IsRemainingExceptional : DynkinFamily → Prop
  | .E6 | .E7 | .F4 | .G2 => True
  | _ => False

theorem classical_or_exceptional (d : DynkinFamily) :
    d.IsClassical ∨ d.IsExceptional := by
  cases d <;> simp [IsClassical, IsExceptional]

theorem exceptional_iff_e8_or_remainingExceptional (d : DynkinFamily) :
    d.IsExceptional ↔ d = .E8 ∨ d.IsRemainingExceptional := by
  cases d <;> simp [IsExceptional, IsRemainingExceptional]

theorem ne_e8_iff_classical_or_remainingExceptional (d : DynkinFamily) :
    d ≠ .E8 ↔ d.IsClassical ∨ d.IsRemainingExceptional := by
  cases d <;> simp [IsClassical, IsRemainingExceptional]

end DynkinFamily

/-- An abstract classifier for an affine group scheme's irreducible Dynkin
family. Constructing this classifier for concrete semisimple simply connected
group schemes is a separate obligation. -/
abbrev DynkinFamilyClassifier :=
  (R A : CommRingCat.{u}) → [HopfAlgebra R A] → DynkinFamily

/-- Restrict a group predicate to objects whose supplied Dynkin-family
classifier is not `E8`. -/
def NonE8GroupCondition
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier) : GroupCondition :=
  fun R A _ =>
    IsSemisimpleSimplyConnected R A ∧ family R A ≠ .E8

/-- A pointwise provider of the Serre-II neutrality conclusion for the
families selected by `Select`. -/
abbrev NeutralityProvider
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (Select : DynkinFamily → Prop) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    IsPerfectFieldCdAtMostTwo R →
    IsSemisimpleSimplyConnected R A →
    Select (family R A) →
    Subsingleton (FpqcH1.{u, u} R A)

/-- A neutrality provider for one exact Dynkin family. -/
abbrev ExactFamilyNeutralityProvider
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (d : DynkinFamily) : Prop :=
  NeutralityProvider IsPerfectFieldCdAtMostTwo
    IsSemisimpleSimplyConnected family (fun e => e = d)

/-- Exact providers for the four classical Dynkin series assemble into the
single classical-family provider used by the broad non-`E8` reduction.

This separates the load-bearing type-`D` input, including trialitarian
`D4`, from the type-`A`, type-`B`, and type-`C` inputs. -/
theorem classicalNeutralityProvider_of_exact_providers
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (a : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .A)
    (b : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .B)
    (c : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .C)
    (d : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .D) :
    NeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family DynkinFamily.IsClassical := by
  intro R A _ hField hGroup hClassical
  generalize hfamily : family R A = e at hClassical
  cases e with
  | A => exact a R A hField hGroup hfamily
  | B => exact b R A hField hGroup hfamily
  | C => exact c R A hField hGroup hfamily
  | D => exact d R A hField hGroup hfamily
  | E6 => simp [DynkinFamily.IsClassical] at hClassical
  | E7 => simp [DynkinFamily.IsClassical] at hClassical
  | E8 => simp [DynkinFamily.IsClassical] at hClassical
  | F4 => simp [DynkinFamily.IsClassical] at hClassical
  | G2 => simp [DynkinFamily.IsClassical] at hClassical

/-- If a provider covers the four classical series and separate providers
cover `E6`, `E7`, `F4`, and `G2`, then Serre II holds for every group
selected by the supplied classifier whose family is not `E8`.

This is an assembly theorem. It constructs neither the classifier nor the
five neutrality providers. -/
theorem conjecture_nonE8_of_family_providers
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (classical :
      NeutralityProvider IsPerfectFieldCdAtMostTwo
        IsSemisimpleSimplyConnected family DynkinFamily.IsClassical)
    (e6 :
      ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
        IsSemisimpleSimplyConnected family .E6)
    (e7 :
      ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
        IsSemisimpleSimplyConnected family .E7)
    (f4 :
      ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
        IsSemisimpleSimplyConnected family .F4)
    (g2 :
      ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
        IsSemisimpleSimplyConnected family .G2) :
    H1Conjecture IsPerfectFieldCdAtMostTwo
      (NonE8GroupCondition IsSemisimpleSimplyConnected family) := by
  rw [h1Conjecture_iff_subsingleton]
  intro R A _ hField hGroup
  rcases hGroup with ⟨hSemisimpleSimplyConnected, hne⟩
  generalize hfamily : family R A = d at hne
  cases d with
  | A =>
      exact classical R A hField hSemisimpleSimplyConnected
        (by simp [hfamily, DynkinFamily.IsClassical])
  | B =>
      exact classical R A hField hSemisimpleSimplyConnected
        (by simp [hfamily, DynkinFamily.IsClassical])
  | C =>
      exact classical R A hField hSemisimpleSimplyConnected
        (by simp [hfamily, DynkinFamily.IsClassical])
  | D =>
      exact classical R A hField hSemisimpleSimplyConnected
        (by simp [hfamily, DynkinFamily.IsClassical])
  | E6 =>
      exact e6 R A hField hSemisimpleSimplyConnected hfamily
  | E7 =>
      exact e7 R A hField hSemisimpleSimplyConnected hfamily
  | E8 =>
      exact (hne rfl).elim
  | F4 =>
      exact f4 R A hField hSemisimpleSimplyConnected hfamily
  | G2 =>
      exact g2 R A hField hSemisimpleSimplyConnected hfamily

/-- The non-`E8` assembly theorem with all four classical Dynkin series
exposed as separate exact-family hypotheses. -/
theorem conjecture_nonE8_of_exact_family_providers
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (a : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .A)
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
  conjecture_nonE8_of_family_providers IsPerfectFieldCdAtMostTwo
    IsSemisimpleSimplyConnected family
    (classicalNeutralityProvider_of_exact_providers
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected family a b c d)
    e6 e7 f4 g2

/-- The full supplied H1 target follows from its non-`E8` restriction
and an exact `E8` neutrality provider.

This is a conditional assembly theorem. In particular, the supplied
`DynkinFamilyClassifier` returns one irreducible family; this declaration
does not construct the classifier or formalize the decomposition of a
semisimple group into absolutely almost simple factors and Weil
restrictions. -/
theorem conjecture_of_nonE8_and_e8
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (nonE8 : H1Conjecture Base (NonE8GroupCondition Group family))
    (e8 : ExactFamilyNeutralityProvider Base Group family .E8) :
    H1Conjecture Base Group := by
  rw [h1Conjecture_iff_subsingleton] at nonE8 ⊢
  intro R A _ hBase hGroup
  by_cases hE8 : family R A = .E8
  · exact e8 R A hBase hGroup hE8
  · exact nonE8 R A hBase ⟨hGroup, hE8⟩

/-- The supplied full H1 target is equivalent to the conjunction of its
non-`E8` restriction and its exact `E8` branch. This is an exact logical
decomposition relative to the supplied one-family classifier. -/
theorem conjecture_iff_nonE8_and_e8
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier) :
    H1Conjecture Base Group ↔
      H1Conjecture Base (NonE8GroupCondition Group family) ∧
        ExactFamilyNeutralityProvider Base Group family .E8 := by
  constructor
  · intro h
    rw [h1Conjecture_iff_subsingleton] at h
    constructor
    · rw [h1Conjecture_iff_subsingleton]
      intro R A _ hBase hNonE8
      exact h R A hBase hNonE8.1
    · intro R A _ hBase hGroup _
      exact h R A hBase hGroup
  · rintro ⟨hNonE8, hE8⟩
    exact conjecture_of_nonE8_and_e8 Base Group family hNonE8 hE8

/-- Classical neutrality together with exact providers for all five exceptional
families assembles to the full supplied H1 target. -/
theorem conjecture_of_family_providers
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (classical :
      NeutralityProvider Base Group family DynkinFamily.IsClassical)
    (e6 : ExactFamilyNeutralityProvider Base Group family .E6)
    (e7 : ExactFamilyNeutralityProvider Base Group family .E7)
    (e8 : ExactFamilyNeutralityProvider Base Group family .E8)
    (f4 : ExactFamilyNeutralityProvider Base Group family .F4)
    (g2 : ExactFamilyNeutralityProvider Base Group family .G2) :
    H1Conjecture Base Group :=
  conjecture_of_nonE8_and_e8 Base Group family
    (conjecture_nonE8_of_family_providers
      Base Group family classical e6 e7 f4 g2)
    e8

/-- Exact neutrality providers for every constructor of the supplied
`DynkinFamily` interface assemble to the full supplied H1 target.
The separate family providers, classifier,
and semisimple factor decomposition remain explicit obligations. -/
theorem conjecture_of_exact_family_providers
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (a : ExactFamilyNeutralityProvider Base Group family .A)
    (b : ExactFamilyNeutralityProvider Base Group family .B)
    (c : ExactFamilyNeutralityProvider Base Group family .C)
    (d : ExactFamilyNeutralityProvider Base Group family .D)
    (e6 : ExactFamilyNeutralityProvider Base Group family .E6)
    (e7 : ExactFamilyNeutralityProvider Base Group family .E7)
    (e8 : ExactFamilyNeutralityProvider Base Group family .E8)
    (f4 : ExactFamilyNeutralityProvider Base Group family .F4)
    (g2 : ExactFamilyNeutralityProvider Base Group family .G2) :
    H1Conjecture Base Group :=
  conjecture_of_nonE8_and_e8 Base Group family
    (conjecture_nonE8_of_exact_family_providers
      Base Group family a b c d e6 e7 f4 g2)
    e8

end RiemannResearch.AlgebraicGeometry.SerreII
