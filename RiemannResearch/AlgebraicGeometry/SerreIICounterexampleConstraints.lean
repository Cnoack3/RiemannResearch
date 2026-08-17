/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIITypeD
import RiemannResearch.AlgebraicGeometry.SerreIIE8TrialityReduction
import RiemannResearch.AlgebraicGeometry.SerreIIE8SolvableIncidence

/-!
# Necessary conditions for a Serre-II counterexample

This module records the strongest counterexample exclusions presently justified
by the project's conditional family providers and `E8` survivor reductions.

For type `D`, a nonneutral class lies in an arbitrary trialitarian form whose
Allen algebra has index four or eight, once the imported nontrialitarian and
Allen-index-one/two providers are supplied. If the sourced degree-one-cycle
input is supplied, the same class witnesses that gcd-one splitting degrees do
not by themselves imply coprime restriction descent.

For `E8`, a nonneutral class cannot be induced from any of the six proper
maximal-rank subsystems. It must realize one of the 31 certified perfect-core
rows and can have none of the following: a common gauge, an anchored fixed
correction, a solvable-incidence certificate containing the gcd-one additive
argument, or a trialitarian `D4 × D4` cubic central correction. The existing
finite certificate then splits the survivor into 27 nonbinary rows and the four
binary-icosahedral table classes `4013`, `4014`, `4015`, and `4017`.

These are necessary conditions relative to the explicit imported reduction
data. This module does not construct the family classifier, algebraic subgroup
embeddings, Galois comparison, Allen algebra, or `E8` survivor reduction.

Source: user-provided Serre-II counterexample audit. The proofs are logical
consequences of the kernel-checked reductions in the imported modules.
-/

universe u x

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- Once the `A`, `B`, `C`, `F4`, and `G2` providers are supplied, a
nonneutral class can occur only in family `D`, `E6`, `E7`, or `E8`. -/
theorem nonneutral_family_eq_D_or_E6_or_E7_or_E8
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (a : ExactFamilyNeutralityProvider Base GroupCondition family .A)
    (b : ExactFamilyNeutralityProvider Base GroupCondition family .B)
    (c : ExactFamilyNeutralityProvider Base GroupCondition family .C)
    (f4 : ExactFamilyNeutralityProvider Base GroupCondition family .F4)
    (g2 : ExactFamilyNeutralityProvider Base GroupCondition family .G2)
    (R A : Type u) [Field R] [CommRing A] [HopfAlgebra R A]
    (hBase : Base R) (hGroup : GroupCondition R A)
    (ξ : GaloisH1 R A)
    (hξ : ξ ≠ GaloisH1.neutral R A) :
    family R A = .D ∨
      family R A = .E6 ∨
      family R A = .E7 ∨
      family R A = .E8 := by
  generalize hfamily : family R A = d
  cases d with
  | A =>
      exact False.elim
        (hξ (@Subsingleton.elim _
          (a R A hBase hGroup hfamily)
          ξ (GaloisH1.neutral R A)))
  | B =>
      exact False.elim
        (hξ (@Subsingleton.elim _
          (b R A hBase hGroup hfamily)
          ξ (GaloisH1.neutral R A)))
  | C =>
      exact False.elim
        (hξ (@Subsingleton.elim _
          (c R A hBase hGroup hfamily)
          ξ (GaloisH1.neutral R A)))
  | D => simp
  | E6 => simp
  | E7 => simp
  | E8 => simp
  | F4 =>
      exact False.elim
        (hξ (@Subsingleton.elim _
          (f4 R A hBase hGroup hfamily)
          ξ (GaloisH1.neutral R A)))
  | G2 =>
      exact False.elim
        (hξ (@Subsingleton.elim _
          (g2 R A hBase hGroup hfamily)
          ξ (GaloisH1.neutral R A)))

/-- A type-`D` nonneutral class surviving the nontrialitarian and low-Allen-
index providers must be trialitarian with Allen index four or eight. -/
theorem typeD_nonneutral_requires_trialitarian_allenIndex_four_or_eight
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (nontrialitarian : TypeDFormNeutralityProvider
      Base GroupCondition family typeDForm TypeDForm.IsNontrialitarian)
    (allenIndex : TrialitarianAllenIndexClassifier)
    (indexCases : TrialitarianAllenIndexCasesProvider
      Base GroupCondition family typeDForm allenIndex)
    (indexOne : TrialitarianAllenIndexNeutralityProvider
      Base GroupCondition family typeDForm allenIndex 1)
    (indexTwo : TrialitarianAllenIndexNeutralityProvider
      Base GroupCondition family typeDForm allenIndex 2)
    (R A : Type u) [Field R] [CommRing A] [HopfAlgebra R A]
    (hBase : Base R) (hGroup : GroupCondition R A)
    (hD : family R A = .D)
    (ξ : GaloisH1 R A)
    (hξ : ξ ≠ GaloisH1.neutral R A) :
    (typeDForm R A).IsTrialitarian ∧
      (allenIndex.index R A = 4 ∨ allenIndex.index R A = 8) := by
  have htrial : (typeDForm R A).IsTrialitarian := by
    rcases TypeDForm.nontrialitarian_or_trialitarian (typeDForm R A) with
      hNon | hTri
    · exact False.elim
        (hξ (@Subsingleton.elim _
          (nontrialitarian R A hBase hGroup hD hNon)
          ξ (GaloisH1.neutral R A)))
    · exact hTri
  refine ⟨htrial, ?_⟩
  rcases indexCases R A hBase hGroup hD htrial with
    hOne | hTwo | hFour | hEight
  · exact False.elim
      (hξ (@Subsingleton.elim _
        (indexOne R A hBase hGroup hD htrial hOne)
        ξ (GaloisH1.neutral R A)))
  · exact False.elim
      (hξ (@Subsingleton.elim _
        (indexTwo R A hBase hGroup hD htrial hTwo)
        ξ (GaloisH1.neutral R A)))
  · exact Or.inl hFour
  · exact Or.inr hEight

/-- Under the degree-one-cycle input, a nonneutral trialitarian class witnesses
failure of coprime-restriction detection. Thus gcd-one splitting cannot by
itself close the arbitrary trialitarian case. -/
theorem trialitarian_nonneutral_refutes_coprime_restriction_descent
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (restrictionData : TrialitarianRestrictionDataClassifier)
    (cycles : TrialitarianDegreeOneCycleProvider
      Base GroupCondition family typeDForm restrictionData)
    (R A : Type u) [Field R] [CommRing A] [HopfAlgebra R A]
    (hBase : Base R) (hGroup : GroupCondition R A)
    (hD : family R A = .D)
    (hTrialitarian : (typeDForm R A).IsTrialitarian)
    (ξ : GaloisH1 R A)
    (hξ : ξ ≠ GaloisH1.neutral R A) :
    ¬ CoprimeRestrictionDetectsBasepoint
      (GaloisH1.neutral R A)
      (restrictionData R A).isFinite
      (restrictionData R A).degree
      (restrictionData R A).LocalClass
      (restrictionData R A).neutral
      (restrictionData R A).restrict := by
  intro descent
  have splitting :=
    trialitarianCoprimeSplittingProvider_of_degreeOneCycles
      Base GroupCondition family typeDForm restrictionData cycles
  exact hξ
    (descent ξ (splitting R A hBase hGroup hD hTrialitarian ξ))

/-- Subject to the displayed established-family and low-index providers, every
nonneutral class is in `E6`, `E7`, `E8`, or an Allen-index-four/eight arbitrary
trialitarian `D4` form. -/
theorem nonneutral_family_is_E6_E7_E8_or_highIndexTrialitarianD
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (a : ExactFamilyNeutralityProvider Base GroupCondition family .A)
    (b : ExactFamilyNeutralityProvider Base GroupCondition family .B)
    (c : ExactFamilyNeutralityProvider Base GroupCondition family .C)
    (f4 : ExactFamilyNeutralityProvider Base GroupCondition family .F4)
    (g2 : ExactFamilyNeutralityProvider Base GroupCondition family .G2)
    (typeDForm : TypeDFormClassifier)
    (nontrialitarian : TypeDFormNeutralityProvider
      Base GroupCondition family typeDForm TypeDForm.IsNontrialitarian)
    (allenIndex : TrialitarianAllenIndexClassifier)
    (indexCases : TrialitarianAllenIndexCasesProvider
      Base GroupCondition family typeDForm allenIndex)
    (indexOne : TrialitarianAllenIndexNeutralityProvider
      Base GroupCondition family typeDForm allenIndex 1)
    (indexTwo : TrialitarianAllenIndexNeutralityProvider
      Base GroupCondition family typeDForm allenIndex 2)
    (R A : Type u) [Field R] [CommRing A] [HopfAlgebra R A]
    (hBase : Base R) (hGroup : GroupCondition R A)
    (ξ : GaloisH1 R A)
    (hξ : ξ ≠ GaloisH1.neutral R A) :
    family R A = .E6 ∨
      family R A = .E7 ∨
      family R A = .E8 ∨
      (family R A = .D ∧
        (typeDForm R A).IsTrialitarian ∧
        (allenIndex.index R A = 4 ∨ allenIndex.index R A = 8)) := by
  rcases nonneutral_family_eq_D_or_E6_or_E7_or_E8
      Base GroupCondition family a b c f4 g2
      R A hBase hGroup ξ hξ with hD | hE6 | hE7 | hE8
  · exact Or.inr (Or.inr (Or.inr
      ⟨hD,
        typeD_nonneutral_requires_trialitarian_allenIndex_four_or_eight
          Base GroupCondition family typeDForm nontrialitarian
          allenIndex indexCases indexOne indexTwo
          R A hBase hGroup hD ξ hξ⟩))
  · exact Or.inl hE6
  · exact Or.inr (Or.inl hE7)
  · exact Or.inr (Or.inr (Or.inl hE8))

/-- Constraints forced on a nonneutral class by supplied
`E8SurvivorReductionData`. The solvable-incidence field uses `IsEmpty` because
a certificate is data rather than a proposition. -/
structure E8CounterexampleConstraints
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral)
    (ξ : X) where
  survivor : E8PerfectCoreSurvivorCase
  realizes : D.realizes ξ survivor
  notInduced :
    ¬ ∃ s, ∃ η : D.induction.H1 s,
      D.induction.induce s η = ξ
  noCommonGauge :
    ¬ (D.reduction ξ survivor realizes).HasCommonGauge
  noAnchoredFixedCorrection :
    ¬ (D.reduction ξ survivor realizes).HasAnchoredFixedCorrection
  noSolvableIncidenceCertificate :
    IsEmpty (D.reduction ξ survivor realizes).SolvableIncidenceCertificate
  noOrbitwiseD4Correction :
    ∀ (G : D4PairCentralGeometry.{u, x} X neutral)
      (P : BinaryD4OrbitReduction G ξ survivor),
      ¬ P.HasRequiredCorrection
  binaryTableClass :
    survivor.IsBinaryIcosahedral →
      survivor.datum.tableClass = 4013 ∨
      survivor.datum.tableClass = 4014 ∨
      survivor.datum.tableClass = 4015 ∨
      survivor.datum.tableClass = 4017

/-- Every nonneutral class classified by supplied `E8` survivor data has a
survivor satisfying all fields of `E8CounterexampleConstraints`. -/
theorem E8SurvivorReductionData.counterexampleConstraints_of_ne
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral)
    {ξ : X} (hξ : ξ ≠ neutral) :
    Nonempty (E8CounterexampleConstraints D ξ) := by
  have hnotInduced :
      ¬ ∃ s, ∃ η : D.induction.H1 s,
        D.induction.induce s η = ξ :=
    D.induction.nonneutral_not_induced D.allSubsystemsSerreII hξ
  have hsurvivor : ∃ survivor, D.realizes ξ survivor := by
    rcases D.classify ξ with hinduced | hsurvivor
    · exact False.elim (hnotInduced hinduced)
    · exact hsurvivor
  obtain ⟨survivor, hrealizes⟩ := hsurvivor
  let P := D.reduction ξ survivor hrealizes
  refine ⟨
    { survivor := survivor
      realizes := hrealizes
      notInduced := hnotInduced
      noCommonGauge := ?_
      noAnchoredFixedCorrection := ?_
      noSolvableIncidenceCertificate := ?_
      noOrbitwiseD4Correction := ?_
      binaryTableClass := ?_ }⟩
  · intro hcommon
    exact hξ (P.eq_basepoint_of_commonGauge hcommon)
  · intro hfixed
    exact hξ (P.eq_basepoint_of_commonGauge
      (P.hasCommonGauge_iff_hasAnchoredFixedCorrection.2 hfixed))
  · exact ⟨fun C =>
      hξ (P.eq_basepoint_of_solvableIncidenceCertificate C)⟩
  · intro G Q hQ
    exact hξ (Q.eq_neutral_of_requiredCorrection hQ)
  · intro hbinary
    exact
      (E8PerfectCoreSurvivorCase.isBinaryIcosahedral_iff_tableClass
        survivor).1 hbinary

/-- The survivor attached to a counterexample lies either in the explicit
four-row binary packet, where every supplied fixed-geometry orbit reduction
lacks its required correction, or in the 27-row complement and lacks a common
gauge. -/
theorem E8CounterexampleConstraints.binary_or_nonbinary
    {X : Type x} {neutral : X}
    {D : E8SurvivorReductionData.{u, x} neutral}
    {ξ : X} (C : E8CounterexampleConstraints D ξ) :
    (C.survivor.IsBinaryIcosahedral ∧
      (C.survivor.datum.tableClass = 4013 ∨
       C.survivor.datum.tableClass = 4014 ∨
       C.survivor.datum.tableClass = 4015 ∨
       C.survivor.datum.tableClass = 4017) ∧
      (∀ (G : D4PairCentralGeometry.{u, x} X neutral)
        (P : BinaryD4OrbitReduction G ξ C.survivor),
        ¬ P.HasRequiredCorrection)) ∨
    (¬ C.survivor.IsBinaryIcosahedral ∧
      ¬ (D.reduction ξ C.survivor C.realizes).HasCommonGauge) := by
  by_cases hbinary : C.survivor.IsBinaryIcosahedral
  · exact Or.inl
      ⟨hbinary, C.binaryTableClass hbinary,
        C.noOrbitwiseD4Correction⟩
  · exact Or.inr ⟨hbinary, C.noCommonGauge⟩

end RiemannResearch.AlgebraicGeometry.SerreII
