/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIIE8TrialityReduction
import RiemannResearch.Logic.PointedKernel

/-!
# Gille cyclic restriction for the E8 survivor packet

This module applies Gille's cyclic relative-kernel theorem at the pointed-set
boundary used by the E8 survivor reduction. Under characteristic zero and
`cd_p(k) ≤ 2` for `p = 2, 3, 5`, Gille proves that for the split E8 group and a
cyclic extension `L/k` of degree 2, 3, or 5 the relative set
`H¹(L/k, E8)` is trivial. Equivalently, the neutral fiber of
`H¹(k, E8) → H¹(L, E8)` is a singleton.

The structure below records a fixed family of such restriction maps and the
resulting trivial-kernel theorem. Lean then proves two consequences:

* a class neutralized by one recorded cyclic restriction is already neutral;
* a nonneutral class remains nonneutral after every recorded cyclic
  restriction.

For the certified E8 packet this replaces the four binary-icosahedral
orbitwise D4-correction obligations by the requirement that each realized
binary class become neutral over one member of a fixed cyclic-prime family.
Together with common gauges for the other twenty-seven rows, this yields the
exact E8 provider and hence the full family-hierarchy reduction.

This is a conditional research reduction. It does not construct the cyclic
extensions, and construct continuous Galois
restriction, or prove that a binary survivor becomes neutral after
restriction. In particular, the existing D4 coordinate-module descent theorem
does not supply that last assertion.

Source for the external `gilleKernel` field:

* Philippe Gille, “Cohomologie galoisienne des groupes quasi-déployés sur des
  corps de dimension cohomologique ≤ 2,” *Compositio Mathematica* 125 (2001),
  Theorem 11, pp. 283–325,
  <https://doi.org/10.1023/A:1002473132282>.
-/

universe u x

namespace RiemannResearch.AlgebraicGeometry.SerreII

open RiemannResearch.Logic

/-- A fixed family of E8 restriction maps to cyclic extensions of supported
prime degree, together with Gille's trivial relative-kernel conclusion.

The algebraic field extensions and continuous Galois cohomology are still
external to the current Galois model. Consequently an inhabitant must only be
constructed from actual cyclic extensions satisfying Gille's hypotheses; the
`degree_eq_two_or_three_or_five` and `gilleKernel` fields expose the exact
theorem used by the subsequent formal argument. -/
structure GilleCyclicE8RestrictionFamily
    (X : Type x) (neutral : X) where
  Index : Type u
  LocalClass : Index → Type u
  localNeutral : ∀ i, LocalClass i
  restrict : ∀ i, X → LocalClass i
  degree : Index → ℕ
  degree_eq_two_or_three_or_five :
    ∀ i, degree i = 2 ∨ degree i = 3 ∨ degree i = 5
  gilleKernel :
    ∀ i, HasTrivialKernel neutral (localNeutral i) (restrict i)

namespace GilleCyclicE8RestrictionFamily

/-- Gille's relative-kernel conclusion in its directly usable form: a class
restricts to the local neutral point exactly when it is globally neutral. -/
theorem restrict_eq_neutral_iff
    {X : Type x} {neutral : X}
    (F : GilleCyclicE8RestrictionFamily.{u, x} X neutral)
    (i : F.Index) (ξ : X) :
    F.restrict i ξ = F.localNeutral i ↔ ξ = neutral :=
  F.gilleKernel i ξ

/-- A class split by one cyclic extension of degree 2, 3, or 5 in the family
is neutral. -/
theorem eq_neutral_of_restrict_eq
    {X : Type x} {neutral : X}
    (F : GilleCyclicE8RestrictionFamily.{u, x} X neutral)
    {ξ : X} (i : F.Index)
    (h : F.restrict i ξ = F.localNeutral i) :
    ξ = neutral :=
  (F.restrict_eq_neutral_iff i ξ).1 h

/-- Counterexample form of Gille's theorem: a nonneutral E8 class cannot
become neutral over any recorded cyclic extension of degree 2, 3, or 5. -/
theorem restrict_neutral_ne_of_ne
    {X : Type x} {neutral : X}
    (F : GilleCyclicE8RestrictionFamily.{u, x} X neutral)
    {ξ : X} (hξ : ξ ≠ neutral) (i : F.Index) :
    F.restrict i ξ ≠ F.localNeutral i := by
  intro h
  exact hξ (F.eq_neutral_of_restrict_eq i h)

end GilleCyclicE8RestrictionFamily

/-- One fixed cyclic-prime restriction family that neutralizes every realized
binary-icosahedral survivor after at least one restriction.

The family is chosen once for the full pointed set. Only the index of a
splitting extension may vary with the realized survivor. This keeps the
Gille kernel theorem separate from the still-open geometric assertion that
the four binary rows split over members of the family. -/
structure BinaryGilleCyclicRestrictionProvider
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral) where
  family : GilleCyclicE8RestrictionFamily.{u, x} X neutral
  restrictionNeutral :
    ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
      (_h : D.realizes ξ survivor),
      survivor.IsBinaryIcosahedral →
        ∃ i : family.Index,
          family.restrict i ξ = family.localNeutral i

namespace E8SurvivorReductionData

/-- The Gille version of the `4 + 27` E8 assembly.

The twenty-seven nonbinary survivor rows are handled by common gauges. Each
of the four binary-icosahedral rows is handled by becoming neutral after one
cyclic restriction of degree 2, 3, or 5, followed by Gille's relative-kernel
theorem. -/
theorem
    eq_neutral_of_nonbinaryCommonGauges_and_binaryGilleCyclicRestrictions
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral)
    (nonbinaryCommonGauge :
      ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
        (_h : D.realizes ξ survivor),
        ¬ survivor.IsBinaryIcosahedral →
          (D.reduction ξ survivor _h).HasCommonGauge)
    (binary : BinaryGilleCyclicRestrictionProvider D)
    (ξ : X) :
    ξ = neutral := by
  rcases D.classify ξ with hInduced | hSurvivor
  · obtain ⟨s, η, hη⟩ := hInduced
    exact
      hη ▸ D.induction.induced_eq_neutral
        D.allSubsystemsSerreII s η
  · obtain ⟨survivor, hrealizes⟩ := hSurvivor
    by_cases hs : survivor.IsBinaryIcosahedral
    · obtain ⟨i, hi⟩ :=
        binary.restrictionNeutral ξ survivor hrealizes hs
      exact binary.family.eq_neutral_of_restrict_eq i hi
    · exact
        (D.reduction ξ survivor hrealizes).eq_basepoint_of_commonGauge
          (nonbinaryCommonGauge ξ survivor hrealizes hs)

end E8SurvivorReductionData

/-- Exact E8 family provider from twenty-seven nonbinary common gauges and
cyclic-prime splitting of the four binary survivors. -/
theorem
    exactFamilyE8_of_nonbinaryCommonGauges_and_binaryGilleCyclicRestrictions
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (reductions :
      ∀ (R A : Type x) [Field R] [CommRing A] [HopfAlgebra R A],
        Base R →
        GroupCondition R A →
        family R A = .E8 →
          E8SurvivorReductionData.{u, x} (GaloisH1.neutral R A))
    (nonbinaryCommonGauge :
      ∀ (R A : Type x) [Field R] [CommRing A] [HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8)
        (ξ : GaloisH1 R A)
        (survivor : E8PerfectCoreSurvivorCase)
        (_h :
          (reductions R A hBase hGroup hE8).realizes ξ survivor),
        ¬ survivor.IsBinaryIcosahedral →
          ((reductions R A hBase hGroup hE8).reduction
            ξ survivor _h).HasCommonGauge)
    (binary :
      ∀ (R A : Type x) [Field R] [CommRing A] [HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8),
          BinaryGilleCyclicRestrictionProvider
            (reductions R A hBase hGroup hE8)) :
    ExactFamilyNeutralityProvider Base GroupCondition family .E8 := by
  intro R A _ _ _ hBase hGroup hE8
  let D := reductions R A hBase hGroup hE8
  have hnonbinary :
      ∀ (ξ : GaloisH1 R A)
        (survivor : E8PerfectCoreSurvivorCase)
        (_h : D.realizes ξ survivor),
        ¬ survivor.IsBinaryIcosahedral →
          (D.reduction ξ survivor _h).HasCommonGauge := by
    intro ξ survivor hrealizes hs
    simpa [D] using
      nonbinaryCommonGauge R A hBase hGroup hE8
        ξ survivor hrealizes hs
  let B : BinaryGilleCyclicRestrictionProvider D := by
    simpa [D] using binary R A hBase hGroup hE8
  constructor
  intro ξ η
  exact
    (D.eq_neutral_of_nonbinaryCommonGauges_and_binaryGilleCyclicRestrictions
      hnonbinary B ξ).trans
    (D.eq_neutral_of_nonbinaryCommonGauges_and_binaryGilleCyclicRestrictions
      hnonbinary B η).symm

/-- Terminal family-hierarchy reduction using Gille on the four binary rows.

The remaining E8 hypotheses are the survivor realization, twenty-seven
nonbinary common gauges, and actual cyclic-prime restriction-neutrality for
the four binary survivors. -/
theorem serreII_of_familyHierarchy_and_binaryGilleCyclicRestrictions
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (hierarchy :
      NonE8FamilyNeutralityHierarchy Base GroupCondition family)
    (reductions :
      ∀ (R A : Type x) [Field R] [CommRing A] [HopfAlgebra R A],
        Base R →
        GroupCondition R A →
        family R A = .E8 →
          E8SurvivorReductionData.{u, x} (GaloisH1.neutral R A))
    (nonbinaryCommonGauge :
      ∀ (R A : Type x) [Field R] [CommRing A] [HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8)
        (ξ : GaloisH1 R A)
        (survivor : E8PerfectCoreSurvivorCase)
        (_h :
          (reductions R A hBase hGroup hE8).realizes ξ survivor),
        ¬ survivor.IsBinaryIcosahedral →
          ((reductions R A hBase hGroup hE8).reduction
            ξ survivor _h).HasCommonGauge)
    (binary :
      ∀ (R A : Type x) [Field R] [CommRing A] [HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8),
          BinaryGilleCyclicRestrictionProvider
            (reductions R A hBase hGroup hE8)) :
    Conjecture Base GroupCondition :=
  hierarchy.conjecture_of_e8
    (exactFamilyE8_of_nonbinaryCommonGauges_and_binaryGilleCyclicRestrictions
      Base GroupCondition family reductions nonbinaryCommonGauge binary)

end RiemannResearch.AlgebraicGeometry.SerreII
