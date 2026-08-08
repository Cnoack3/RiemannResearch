/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.PointFields
import RiemannResearch.AlgebraicGeometry.SerreIIConjecture

/-!
# Conditional non-E8 scope for Serre's Conjecture II

This module records the precise logical assembly behind a published non-E8
scope. The base hypotheses include characteristic different from two and the
relevant period-index property at the primes two and three. The group
hypotheses require no E8 factor and require every exceptional factor other
than G2 to be quasi-split.

The project does not yet formalize those intrinsic field and group predicates,
the period-index theorem producing index one, or the Black-style theorem
turning a zero-cycle of degree one into a rational point. They are therefore
parameters of the checked implication below rather than hidden axioms.
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII.NonE8

/-- The base-field scope used by the conditional published non-E8 reduction. -/
def PublishedBaseScope
    (IsPerfectFieldCdAtMostTwo CharacteristicNotTwo
      PeriodIndexAtTwoAndThree : BaseCondition) : BaseCondition :=
  fun R =>
    IsPerfectFieldCdAtMostTwo R ∧
    CharacteristicNotTwo R ∧
    PeriodIndexAtTwoAndThree R

/-- The group scope used by the conditional published non-E8 reduction. -/
def PublishedGroupScope
    (IsSemisimpleSimplyConnected HasNoE8Factor
      ExceptionalFactorsExceptG2AreQuasiSplit : GroupCondition) :
    GroupCondition :=
  fun R A _ =>
    IsSemisimpleSimplyConnected R A ∧
    HasNoE8Factor R A ∧
    ExceptionalFactorsExceptG2AreQuasiSplit R A

/-- Abstract finite splitting-field data attached to one fpqc H1 class. -/
structure SplittingFieldData
    (R A : CommRingCat.{u}) [HopfAlgebra R A]
    (ξ : FpqcH1.{u, u} R A) where
  Extension : Type u
  isFinite : Extension → Prop
  degree : Extension → ℕ
  splits : Extension → Prop

/-- The gcd of the finite splitting-field degrees is one. -/
def SplittingFieldData.IndexOne
    {R A : CommRingCat.{u}} [HopfAlgebra R A]
    {ξ : FpqcH1.{u, u} R A} (D : SplittingFieldData R A ξ) : Prop :=
  pointFieldIndex D.isFinite D.degree D.splits = 1

/-- Conditional assembly of the published non-E8/period-index scope of
Serre II.

The first provider is the period-index/norm input producing a zero-cycle of
degree one. The second is the no-E8, quasi-split exceptional-factor descent
input turning that zero-cycle into neutrality. Both remain explicit until
their algebraic-group content is formalized. -/
theorem serreII_of_periodIndex_and_nonE8_indexOneDescent
    (IsPerfectFieldCdAtMostTwo CharacteristicNotTwo
      PeriodIndexAtTwoAndThree : BaseCondition)
    (IsSemisimpleSimplyConnected HasNoE8Factor
      ExceptionalFactorsExceptG2AreQuasiSplit : GroupCondition)
    (splittingFields :
      ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A]
        (ξ : FpqcH1.{u, u} R A), SplittingFieldData R A ξ)
    (indexOne_of_periodIndex :
      ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
        PublishedBaseScope IsPerfectFieldCdAtMostTwo CharacteristicNotTwo
          PeriodIndexAtTwoAndThree R →
        PublishedGroupScope IsSemisimpleSimplyConnected HasNoE8Factor
          ExceptionalFactorsExceptG2AreQuasiSplit R A →
        ∀ ξ, (splittingFields R A ξ).IndexOne)
    (neutral_of_indexOne :
      ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
        PublishedBaseScope IsPerfectFieldCdAtMostTwo CharacteristicNotTwo
          PeriodIndexAtTwoAndThree R →
        PublishedGroupScope IsSemisimpleSimplyConnected HasNoE8Factor
          ExceptionalFactorsExceptG2AreQuasiSplit R A →
        ∀ ξ, (splittingFields R A ξ).IndexOne →
          ξ = FpqcH1.neutral R A) :
    Conjecture
      (PublishedBaseScope IsPerfectFieldCdAtMostTwo CharacteristicNotTwo
        PeriodIndexAtTwoAndThree)
      (PublishedGroupScope IsSemisimpleSimplyConnected HasNoE8Factor
        ExceptionalFactorsExceptG2AreQuasiSplit) := by
  intro R A _ hBase hGroup ξ
  exact neutral_of_indexOne R A hBase hGroup ξ
    (indexOne_of_periodIndex R A hBase hGroup ξ)

end RiemannResearch.AlgebraicGeometry.SerreII.NonE8
