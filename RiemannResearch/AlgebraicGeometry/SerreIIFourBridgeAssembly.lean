/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIINonE8

/-!
# The four residual bridge boundary for Serre II

This module sharpens the existing Dynkin-family assembly theorem to the exact
four-stratum boundary isolated by the full-proof blueprint.  Relative to a
supplied irreducible-family classifier, the only residual providers are:

* high-index trialitarian `D₄` inside family `D`;
* high-index `E₆`;
* index-eight `E₇`;
* the entire `E₈` branch.

The first three families are equipped with a two-valued stratum classifier.
Its `established` value is intended to contain the already known cases, while
its `residual` value is intended to contain exactly the corresponding bridge
stratum.  For example, the family-`D` classifier should mark trialitarian
Allen indices four and eight as residual and every established type-`D` case
as established.

The resulting theorem is an exact logical equivalence: after providers for the
established strata and for `A`, `B`, `C`, `F₄`, and `G₂` are fixed, the full
one-family-classifier `Conjecture` is equivalent to the conjunction of the four
residual providers.  No geometric bridge is asserted or hidden in this file.
In particular, this is the unconditional assembly shell around the four open
mathematical theorems, not a proof of those theorems.
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- Whether a form belongs to an already established stratum or to the single
residual bridge stratum for its Dynkin family. -/
inductive BridgeStratum
  | established
  | residual
  deriving DecidableEq

namespace BridgeStratum

/-- Select the already established stratum. -/
def IsEstablished : BridgeStratum → Prop
  | .established => True
  | .residual => False

/-- Select the residual bridge stratum. -/
def IsResidual : BridgeStratum → Prop
  | .established => False
  | .residual => True

/-- Every supplied form lies in exactly one of the two strata. -/
theorem established_or_residual (s : BridgeStratum) :
    s.IsEstablished ∨ s.IsResidual := by
  cases s <;> simp [IsEstablished, IsResidual]

end BridgeStratum

/-- A supplied classifier separating the established and residual strata of
one irreducible Dynkin family.  Constructing the classifier from Tits, Allen,
or trialitarian data is a separate formalization obligation. -/
abbrev FamilyStratumClassifier :=
  (K A : Type u) → [Field K] → [CommRing A] → [HopfAlgebra K A] →
    BridgeStratum

/-- Neutrality for one exact Dynkin family and one selected stratum. -/
abbrev ExactFamilyStratumNeutralityProvider
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (d : DynkinFamily)
    (stratum : FamilyStratumClassifier)
    (Select : BridgeStratum → Prop) : Prop :=
  ∀ (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A],
    Base K →
    Group K A →
    family K A = d →
    Select (stratum K A) →
    Subsingleton (GaloisH1 K A)

/-- Providers for the established and residual strata assemble into the exact
neutrality provider for the whole Dynkin family. -/
theorem exactFamilyNeutralityProvider_of_strata
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (d : DynkinFamily)
    (stratum : FamilyStratumClassifier)
    (established : ExactFamilyStratumNeutralityProvider
      Base Group family d stratum BridgeStratum.IsEstablished)
    (residual : ExactFamilyStratumNeutralityProvider
      Base Group family d stratum BridgeStratum.IsResidual) :
    ExactFamilyNeutralityProvider Base Group family d := by
  intro K A _ _ _ hBase hGroup hFamily
  rcases BridgeStratum.established_or_residual
      (stratum K A) with hEstablished | hResidual
  · exact established K A hBase hGroup hFamily hEstablished
  · exact residual K A hBase hGroup hFamily hResidual

/-- The four genuinely residual cohomological providers.

The field names record the intended mathematical content:

* `trialitarianD4` is the cohomological consequence of the high-index
  trialitarian zero-cycle/rigidity bridge;
* `highIndexE6` is the consequence of fixed-Tits-fibre rigidity;
* `indexEightE7` is the consequence of the three-quaternion realization;
* `eviiiOddE8` is the consequence of odd-degree descent for twisted EVIII.

This structure packages only their exact `GaloisH1` conclusions. -/
structure FourBridgeBoundary
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (dStratum e6Stratum e7Stratum : FamilyStratumClassifier) : Prop where
  trialitarianD4 : ExactFamilyStratumNeutralityProvider
    Base Group family .D dStratum BridgeStratum.IsResidual
  highIndexE6 : ExactFamilyStratumNeutralityProvider
    Base Group family .E6 e6Stratum BridgeStratum.IsResidual
  indexEightE7 : ExactFamilyStratumNeutralityProvider
    Base Group family .E7 e7Stratum BridgeStratum.IsResidual
  eviiiOddE8 : ExactFamilyNeutralityProvider
    Base Group family .E8

/-- The full supplied Serre-II conjecture restricts to all four residual
providers.  This direction uses no established-stratum hypothesis. -/
theorem fourBridgeBoundary_of_conjecture
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (dStratum e6Stratum e7Stratum : FamilyStratumClassifier)
    (h : Conjecture Base Group) :
    FourBridgeBoundary Base Group family dStratum e6Stratum e7Stratum := by
  rw [conjecture_iff_subsingleton] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K A _ _ _ hBase hGroup _ _
    exact h K A hBase hGroup
  · intro K A _ _ _ hBase hGroup _ _
    exact h K A hBase hGroup
  · intro K A _ _ _ hBase hGroup _ _
    exact h K A hBase hGroup
  · intro K A _ _ _ hBase hGroup _
    exact h K A hBase hGroup

/-- The established families and strata, together with the four residual
providers, imply the full supplied one-family-classifier Serre-II conjecture.

This is the Lean assembly theorem corresponding to the four-bridge blueprint.
It does not construct the family/stratum classifiers, the semisimple-factor
and Weil-restriction decomposition, or any of the four geometric bridges. -/
theorem conjecture_of_fourBridgeBoundary
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (dStratum e6Stratum e7Stratum : FamilyStratumClassifier)
    (a : ExactFamilyNeutralityProvider Base Group family .A)
    (b : ExactFamilyNeutralityProvider Base Group family .B)
    (c : ExactFamilyNeutralityProvider Base Group family .C)
    (dEstablished : ExactFamilyStratumNeutralityProvider
      Base Group family .D dStratum BridgeStratum.IsEstablished)
    (e6Established : ExactFamilyStratumNeutralityProvider
      Base Group family .E6 e6Stratum BridgeStratum.IsEstablished)
    (e7Established : ExactFamilyStratumNeutralityProvider
      Base Group family .E7 e7Stratum BridgeStratum.IsEstablished)
    (f4 : ExactFamilyNeutralityProvider Base Group family .F4)
    (g2 : ExactFamilyNeutralityProvider Base Group family .G2)
    (bridges : FourBridgeBoundary
      Base Group family dStratum e6Stratum e7Stratum) :
    Conjecture Base Group :=
  conjecture_of_exact_family_providers Base Group family
    a b c
    (exactFamilyNeutralityProvider_of_strata
      Base Group family .D dStratum dEstablished bridges.trialitarianD4)
    (exactFamilyNeutralityProvider_of_strata
      Base Group family .E6 e6Stratum e6Established bridges.highIndexE6)
    (exactFamilyNeutralityProvider_of_strata
      Base Group family .E7 e7Stratum e7Established bridges.indexEightE7)
    bridges.eviiiOddE8 f4 g2

/-- Relative to the established family and stratum providers, the full
supplied Serre-II conjecture is exactly equivalent to the four residual bridge
providers. -/
theorem conjecture_iff_fourBridgeBoundary
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (dStratum e6Stratum e7Stratum : FamilyStratumClassifier)
    (a : ExactFamilyNeutralityProvider Base Group family .A)
    (b : ExactFamilyNeutralityProvider Base Group family .B)
    (c : ExactFamilyNeutralityProvider Base Group family .C)
    (dEstablished : ExactFamilyStratumNeutralityProvider
      Base Group family .D dStratum BridgeStratum.IsEstablished)
    (e6Established : ExactFamilyStratumNeutralityProvider
      Base Group family .E6 e6Stratum BridgeStratum.IsEstablished)
    (e7Established : ExactFamilyStratumNeutralityProvider
      Base Group family .E7 e7Stratum BridgeStratum.IsEstablished)
    (f4 : ExactFamilyNeutralityProvider Base Group family .F4)
    (g2 : ExactFamilyNeutralityProvider Base Group family .G2) :
    Conjecture Base Group ↔
      FourBridgeBoundary Base Group family dStratum e6Stratum e7Stratum := by
  constructor
  · intro h
    exact fourBridgeBoundary_of_conjecture
      Base Group family dStratum e6Stratum e7Stratum h
  · intro bridges
    exact conjecture_of_fourBridgeBoundary
      Base Group family dStratum e6Stratum e7Stratum
      a b c dEstablished e6Established e7Established f4 g2 bridges

end RiemannResearch.AlgebraicGeometry.SerreII
