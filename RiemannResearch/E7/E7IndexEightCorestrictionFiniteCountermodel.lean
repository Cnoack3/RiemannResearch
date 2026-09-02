/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.E7IndexEightCorestrictionAffineReduction

/-!
# A finite no-go model for the abstract E7 transfer axioms

This finite `F_2` model has the numerical index pattern of the hard E7 row,
middle-exact split restriction--corestriction, conjugation-stable quaternion
loci, an ordinary two-quaternion factorization of the restricted Clifford
label, and a quaternion point in the prescribed corestriction fibre. It still
has no corestriction-linked lift.

The model proves that additive transfer identities, exactness, and numerical
index bounds alone cannot establish the missing field theorem. It is not a
Brauer group of a field and is not a counterexample to E7 or Serre II.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket.FiniteCountermodel

abbrev F2 := ZMod 2
abbrev A3 := Fin 3 → F2
abbrev B3 := A3 × A3

def weight (a : A3) : Nat :=
  ((Finset.univ : Finset (Fin 3)).filter fun i => a i ≠ 0).card

def symbolicIndex (a : A3) : Nat := 2 ^ weight a
def IsQuaternionA (a : A3) : Prop := weight a ≤ 1

private instance isQuaternionADecidable (a : A3) :
    Decidable (IsQuaternionA a) :=
  inferInstanceAs (Decidable (weight a ≤ 1))

def IsQuaternionB : B3 → Prop :=
  ComponentwiseQuaternionClasses IsQuaternionA

private instance isQuaternionBDecidable (p : B3) :
    Decidable (IsQuaternionB p) :=
  inferInstanceAs (Decidable (IsQuaternionA p.1 ∧ IsQuaternionA p.2))

def indexModel : BrauerIndexModel A3 where
  index := symbolicIndex
  index_zero := by decide
  index_add_le_mul := by decide

def transfer : QuadraticBrauerTransferModel A3 B3 :=
  splitQuadraticBrauerTransferModel

def q1 : A3 := ![1, 0, 0]
def q2 : A3 := ![0, 1, 0]
def q3 : A3 := ![0, 0, 1]
def alpha : A3 := q2 + q3
def beta : A3 := q1 + q2
def r23 : B3 := (q2, q3)
def r32 : B3 := (q3, q2)

/-- The designated triple has quaternion entries, total index eight, and all
three trialitarian packet labels of index four. -/
theorem indexModel_isHard :
    IsQuaternionA q1 ∧ IsQuaternionA q2 ∧ IsQuaternionA q3 ∧
      indexModel.index (q1 + q2 + q3) = 8 ∧
      indexModel.index alpha = 4 ∧ indexModel.index beta = 4 ∧
      indexModel.index (alpha + beta) = 4 := by
  decide

theorem quaternionClassesHaveIndexAtMostTwo :
    QuaternionClassesHaveIndexAtMostTwo indexModel IsQuaternionA := by
  change ∀ q : A3, IsQuaternionA q → indexModel.index q ≤ 2
  decide

/-- The split transfer has the full middle exactness used by the affine-fibre
reduction. -/
theorem splitTransfer_exact :
    ∀ x : B3, transfer.cor x = 0 ↔ ∃ a : A3, transfer.res a = x := by
  decide

theorem conjugation_preserves :
    ConjugationPreservesQuaternionClasses transfer IsQuaternionB := by
  intro r hr
  exact ⟨hr.2, hr.1⟩

theorem restriction_preserves :
    ∀ a : A3, IsQuaternionA a → IsQuaternionB (transfer.res a) := by
  intro a ha
  exact ⟨ha, ha⟩

/-- There are exactly two quaternion points in the prescribed
corestriction fibre, exchanged by conjugation. -/
theorem alpha_quaternion_fibre :
    ∀ r : B3,
      (IsQuaternionB r ∧ transfer.cor r = alpha) ↔
        r = r23 ∨ r = r32 := by
  decide

/-- The restricted target label does have an ordinary two-quaternion
factorization; it is the prescribed fibre condition that fails. -/
theorem restrictedBeta_hasOrdinaryFactorization :
    ∃ u v : B3, IsQuaternionB u ∧ IsQuaternionB v ∧
      u + v = transfer.res beta := by
  refine ⟨(q1, q1), (q2, q2), ?_⟩
  decide

/-- Every beta-directed quaternion chord has corestriction zero or beta, never
the independent prescribed class alpha. -/
theorem betaTranslation_allowedCorestrictions :
    ∀ r : B3,
      IsQuaternionB r → IsQuaternionB (r + transfer.res beta) →
        transfer.cor r = 0 ∨ transfer.cor r = beta := by
  decide

/-- Even with a quaternion point in the correct fibre, the hard numerical
triple has no prescribed-corestriction linked lift. -/
theorem hardIndexEight_noPrescribedCorestrictionLift :
    (∃ r : B3, IsQuaternionB r ∧ transfer.cor r = alpha) ∧
      ¬ HasCorestrictionLinkedQuaternionLift
        transfer IsQuaternionB alpha beta := by
  constructor
  · exact ⟨r23, by decide⟩
  · change ¬ ∃ r : B3,
      IsQuaternionB r ∧ transfer.cor r = alpha ∧
        IsQuaternionB (r + transfer.res beta)
    let d : Decidable (∃ r : B3,
        IsQuaternionB r ∧ transfer.cor r = alpha ∧
          IsQuaternionB (r + transfer.res beta)) :=
      Fintype.decidableExistsFintype
    exact @of_decide_eq_false _ d (by decide)

end RiemannResearch.E7.QuaternionTrialityPacket.FiniteCountermodel
