/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIITypeD

/-!
# Trialitarian Serre II under a hereditary period-index hypothesis

This module records the narrower arbitrary-trialitarian route of
Colliot-Thélène--Gille--Parimala, *Arithmetic of linear algebraic groups over
two-dimensional geometric fields*, Theorem 1.2(ii),
https://www.math.uni-bielefeld.de/lag/man/107.pdf.

The source theorem assumes characteristic zero, cohomological dimension at
most two, and index equal to exponent for every 2-primary central simple
algebra over every finite field extension. For arbitrary simply connected
forms of type ³D₄ and ⁶D₄ it concludes H¹ = 1.

The proof uses the hereditary period-index premise to force the associated
Allen algebra to have index one or two. The index-one branch is quasi-split;
the index-two branch is Gille, *Cohomologie galoisienne des groupes
quasi-déployés sur des corps de dimension cohomologique ≤ 2*, Theorem 8,
https://doi.org/10.1112/S0010437X01000112.

Mathlib currently has the carrier of the Brauer group, central simple
algebras, and Brauer equivalence, but not the Brauer-group operation, scalar
extension, or mathematical period and index. Accordingly, the intrinsic
field predicates and the Allen-index classifier below remain explicit
interfaces. The kernel-checked content is the index-one/index-two branch
reduction, exact type-D assembly, and its connection to the non-E8 theorem.
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- The narrower CTGP field scope: characteristic zero and cohomological
dimension at most two, together with index equal to exponent for every
2-primary central simple algebra over every finite extension. -/
def trialitarianPeriodIndexBaseCondition
    (IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions : BaseCondition) :
    BaseCondition :=
  fun R =>
    IsCharacteristicZeroCdAtMostTwo R ∧
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions R

/-- An abstract classifier for the index of the Allen algebra attached to a
candidate trialitarian group.

The positivity field records the elementary fact that a central simple
algebra has positive index. Constructing this classifier from actual Allen
algebras and Mathlib's future Brauer period/index API remains open. -/
structure TrialitarianAllenIndexClassifier where
  index : (R A : CommRingCat.{u}) → [HopfAlgebra R A] → ℕ
  index_pos : ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    0 < index R A

/-- Every selected arbitrary trialitarian form has Allen-algebra index at most
two on the supplied base-field scope. -/
abbrev TrialitarianAllenIndexAtMostTwoProvider
    (Base : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (allenIndex : TrialitarianAllenIndexClassifier) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    Base R →
    IsSemisimpleSimplyConnected R A →
    family R A = .D →
    (typeDForm R A).IsTrialitarian →
    allenIndex.index R A ≤ 2

/-- Neutrality for the selected arbitrary trialitarian forms whose Allen
algebra has the specified index. The cases one and two correspond respectively
to the quasi-split branch and Gille's index-two theorem. -/
abbrev TrialitarianAllenIndexNeutralityProvider
    (Base : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (allenIndex : TrialitarianAllenIndexClassifier)
    (n : ℕ) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    Base R →
    IsSemisimpleSimplyConnected R A →
    family R A = .D →
    (typeDForm R A).IsTrialitarian →
    allenIndex.index R A = n →
    Subsingleton (FpqcH1.{u, u} R A)

/-- The proof-extracted CTGP arithmetic step: the hereditary 2-primary
index-equals-exponent hypothesis forces the trialitarian Allen algebra to have
index at most two. -/
abbrev TrialitarianAllenIndexAtMostTwoFromPeriodIndexProvider
    (IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (allenIndex : TrialitarianAllenIndexClassifier) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    IsCharacteristicZeroCdAtMostTwo R →
    HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions R →
    IsSemisimpleSimplyConnected R A →
    family R A = .D →
    (typeDForm R A).IsTrialitarian →
    allenIndex.index R A ≤ 2

/-- The sourced period-index arithmetic step supplies the Allen-index bound on
the combined CTGP field scope. -/
theorem trialitarianAllenIndexAtMostTwoProvider_of_twoPrimaryIndexEqualsExponent
    (IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (allenIndex : TrialitarianAllenIndexClassifier)
    (bound : TrialitarianAllenIndexAtMostTwoFromPeriodIndexProvider
      IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions
      IsSemisimpleSimplyConnected family typeDForm allenIndex) :
    TrialitarianAllenIndexAtMostTwoProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family typeDForm allenIndex := by
  intro R A _ hBase hGroup hD hTrialitarian
  exact bound R A hBase.1 hBase.2 hGroup hD hTrialitarian

/-- A positive Allen index bounded by two is either one or two, so neutrality
on those two branches gives neutrality for every arbitrary trialitarian
form. -/
theorem trialitarianNeutralityProvider_of_allenIndexAtMostTwo
    (Base : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (allenIndex : TrialitarianAllenIndexClassifier)
    (atMostTwo : TrialitarianAllenIndexAtMostTwoProvider
      Base IsSemisimpleSimplyConnected family typeDForm allenIndex)
    (indexOne : TrialitarianAllenIndexNeutralityProvider
      Base IsSemisimpleSimplyConnected family typeDForm allenIndex 1)
    (indexTwo : TrialitarianAllenIndexNeutralityProvider
      Base IsSemisimpleSimplyConnected family typeDForm allenIndex 2) :
    TypeDFormNeutralityProvider
      Base IsSemisimpleSimplyConnected family typeDForm
      TypeDForm.IsTrialitarian := by
  intro R A _ hBase hGroup hD hTrialitarian
  by_cases hOne : allenIndex.index R A = 1
  · exact indexOne R A hBase hGroup hD hTrialitarian hOne
  · have hTwo : allenIndex.index R A = 2 := by
      apply Nat.le_antisymm
      · exact atMostTwo R A hBase hGroup hD hTrialitarian
      · apply (Nat.two_le_iff (allenIndex.index R A)).2
        exact ⟨Nat.ne_of_gt (allenIndex.index_pos R A), hOne⟩
    exact indexTwo R A hBase hGroup hD hTrialitarian hTwo

/-- The CTGP period-index step, the quasi-split index-one branch, and Gille's
index-two branch imply neutrality for arbitrary simply connected ³D₄ and ⁶D₄
forms on the narrower field scope. -/
theorem trialitarianNeutralityProvider_of_twoPrimaryIndexEqualsExponent
    (IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (allenIndex : TrialitarianAllenIndexClassifier)
    (bound : TrialitarianAllenIndexAtMostTwoFromPeriodIndexProvider
      IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions
      IsSemisimpleSimplyConnected family typeDForm allenIndex)
    (indexOne : TrialitarianAllenIndexNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family typeDForm allenIndex 1)
    (indexTwo : TrialitarianAllenIndexNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family typeDForm allenIndex 2) :
    TypeDFormNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family typeDForm
      TypeDForm.IsTrialitarian :=
  trialitarianNeutralityProvider_of_allenIndexAtMostTwo
    (trialitarianPeriodIndexBaseCondition
      IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
    IsSemisimpleSimplyConnected family typeDForm allenIndex
    (trialitarianAllenIndexAtMostTwoProvider_of_twoPrimaryIndexEqualsExponent
      IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions
      IsSemisimpleSimplyConnected family typeDForm allenIndex bound)
    indexOne indexTwo

/-- Nontrialitarian type-D neutrality and the narrower CTGP trialitarian route
assemble into the exact family-D provider. -/
theorem exactFamilyD_of_nontrialitarian_and_twoPrimaryIndexEqualsExponent
    (IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (nontrialitarian : TypeDFormNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family typeDForm
      TypeDForm.IsNontrialitarian)
    (allenIndex : TrialitarianAllenIndexClassifier)
    (bound : TrialitarianAllenIndexAtMostTwoFromPeriodIndexProvider
      IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions
      IsSemisimpleSimplyConnected family typeDForm allenIndex)
    (indexOne : TrialitarianAllenIndexNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family typeDForm allenIndex 1)
    (indexTwo : TrialitarianAllenIndexNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family typeDForm allenIndex 2) :
    ExactFamilyNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family .D :=
  exactFamilyD_of_typeD_form_providers
    (trialitarianPeriodIndexBaseCondition
      IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
    IsSemisimpleSimplyConnected family typeDForm nontrialitarian
    (trialitarianNeutralityProvider_of_twoPrimaryIndexEqualsExponent
      IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions
      IsSemisimpleSimplyConnected family typeDForm allenIndex
      bound indexOne indexTwo)

/-- The non-E8 assembly with type D supplied by the narrower characteristic
zero hereditary period-index route. -/
theorem conjecture_nonE8_of_typeA_typeB_and_typeD_periodIndex
    (IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeAForm : TypeAFormClassifier)
    (innerA : TypeAFormNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family typeAForm TypeAForm.IsInner)
    (outerA : TypeAFormNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family typeAForm TypeAForm.IsOuter)
    (typeBForm : TypeBFormClassifier)
    (rankB : ∀ n, 0 < n →
      TypeBRankNeutralityProvider
        (trialitarianPeriodIndexBaseCondition
          IsCharacteristicZeroCdAtMostTwo
          HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
        IsSemisimpleSimplyConnected family typeBForm n)
    (c : ExactFamilyNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family .C)
    (typeDForm : TypeDFormClassifier)
    (nontrialitarianD : TypeDFormNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family typeDForm
      TypeDForm.IsNontrialitarian)
    (allenIndex : TrialitarianAllenIndexClassifier)
    (allenIndexBound : TrialitarianAllenIndexAtMostTwoFromPeriodIndexProvider
      IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions
      IsSemisimpleSimplyConnected family typeDForm allenIndex)
    (allenIndexOne : TrialitarianAllenIndexNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family typeDForm allenIndex 1)
    (allenIndexTwo : TrialitarianAllenIndexNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family typeDForm allenIndex 2)
    (e6 : ExactFamilyNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family .E6)
    (e7 : ExactFamilyNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family .E7)
    (f4 : ExactFamilyNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family .F4)
    (g2 : ExactFamilyNeutralityProvider
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      IsSemisimpleSimplyConnected family .G2) :
    Conjecture
      (trialitarianPeriodIndexBaseCondition
        IsCharacteristicZeroCdAtMostTwo
        HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
      (NonE8GroupCondition IsSemisimpleSimplyConnected family) :=
  conjecture_nonE8_of_typeA_and_typeB_form_providers
    (trialitarianPeriodIndexBaseCondition
      IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions)
    IsSemisimpleSimplyConnected family
    typeAForm innerA outerA typeBForm rankB c
    (exactFamilyD_of_nontrialitarian_and_twoPrimaryIndexEqualsExponent
      IsCharacteristicZeroCdAtMostTwo
      HasTwoPrimaryIndexEqualsExponentOverFiniteExtensions
      IsSemisimpleSimplyConnected family typeDForm nontrialitarianD
      allenIndex allenIndexBound allenIndexOne allenIndexTwo)
    e6 e7 f4 g2

end RiemannResearch.AlgebraicGeometry.SerreII
