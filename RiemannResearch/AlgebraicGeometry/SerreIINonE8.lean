/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.SerreIIConjecture

/-!
# Remaining non-E8 candidates for Serre's Conjecture II

The current mathematical audit isolates four arbitrary-form families:
trialitarian D4, E6, E7, and E8. This module proves the exact assembly statement
that explicit proofs of the first three families settle every remaining non-E8
candidate.

It does not claim that the D4, E6, or E7 inputs have already been formalized.
Each appears as a load-bearing hypothesis, and the E8 family is excluded by
the conclusion's group scope.
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII.NonE8

/-- The arbitrary-form families still isolated by the current Serre II audit. -/
inductive RemainingFamily where
  | trialitarianD4
  | e6
  | e7
  | e8
  deriving DecidableEq

/-- A classifier assigning one remaining family to an affine group scheme. -/
abbrev FamilyClassifier :=
  (R A : CommRingCat.{u}) → [HopfAlgebra R A] → RemainingFamily

/-- Among the remaining candidates, being non-E8 means being D4, E6, or E7. -/
theorem remainingFamily_ne_e8_iff (family : RemainingFamily) :
    family ≠ .e8 ↔
      family = .trialitarianD4 ∨ family = .e6 ∨ family = .e7 := by
  cases family <;> simp

/-- Semisimple simply connected groups classified by a remaining family other
than E8. -/
def RemainingNonE8GroupScope
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : FamilyClassifier) : GroupCondition :=
  fun R A _ =>
    IsSemisimpleSimplyConnected R A ∧ family R A ≠ .e8

/-- If Serre II is supplied for the remaining trialitarian D4, E6, and E7
families, then it holds for every remaining non-E8 candidate.

The three family hypotheses are deliberately explicit: the current project
does not contain their algebraic-group proofs. The E8 branch is excluded by
the conclusion's group scope. -/
theorem serreII_for_remaining_nonE8_candidates
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : FamilyClassifier)
    (trialitarianD4_case :
      ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
        IsPerfectFieldCdAtMostTwo R →
        IsSemisimpleSimplyConnected R A →
        family R A = .trialitarianD4 →
        ∀ ξ : FpqcH1.{u, u} R A, ξ = FpqcH1.neutral R A)
    (e6_case :
      ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
        IsPerfectFieldCdAtMostTwo R →
        IsSemisimpleSimplyConnected R A →
        family R A = .e6 →
        ∀ ξ : FpqcH1.{u, u} R A, ξ = FpqcH1.neutral R A)
    (e7_case :
      ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
        IsPerfectFieldCdAtMostTwo R →
        IsSemisimpleSimplyConnected R A →
        family R A = .e7 →
        ∀ ξ : FpqcH1.{u, u} R A, ξ = FpqcH1.neutral R A) :
    Conjecture IsPerfectFieldCdAtMostTwo
      (RemainingNonE8GroupScope IsSemisimpleSimplyConnected family) := by
  intro R A _ hField hGroup ξ
  rcases (remainingFamily_ne_e8_iff (family R A)).mp hGroup.2 with
    hD4 | hE6 | hE7
  · exact trialitarianD4_case R A hField hGroup.1 hD4 ξ
  · exact e6_case R A hField hGroup.1 hE6 ξ
  · exact e7_case R A hField hGroup.1 hE7 ξ

end RiemannResearch.AlgebraicGeometry.SerreII.NonE8
