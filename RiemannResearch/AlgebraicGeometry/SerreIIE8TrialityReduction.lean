/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIIE8Completion
import RiemannResearch.GroupCohomology.TrialitarianCentralResidue

/-!
# Trialitarian D4-pair reduction for the binary E8 survivors

This module isolates the strongest presently honest consequence of the
D4 × D4 route to the remaining E8 case of Serre II.

The committed finite certificate has four projective-order-60 survivor rows.
For those rows, a supplied reduction through a central quotient of two Type-D
H1 sets is neutral as soon as its two-primary central obstruction has the
cubic correction predicted by triality. The other twenty-seven rows retain
the existing common-gauge obligation.

The proof uses only the arithmetic fact that 3 • z = z for two-torsion z. It
does not construct Spin₈, the central quotient (Spin₈ × Spin₈) / μ₂², its
embedding in E8, the connecting H2 obstruction, or the required cubic boundary
theorem.

Sources:

* User-provided handoff, *From the D4 Discriminant–Triality Theorem to
  Serre II for E8*; this supports the reduction architecture.
* Skip Garibaldi, *E8, the most exceptional group*,
  <https://www.garibaldibros.com/linked-files/e8.pdf>; this supports the
  D4-by-D4 central-quotient architecture, not the torsor reduction asserted
  here as explicit data.
-/

universe u x

namespace RiemannResearch.AlgebraicGeometry.SerreII

open RiemannResearch.GroupCohomology

/-- A supplied reduction of one pointed class through a central quotient of
two Type-D H1 sets.

This is an interface, not a construction of the relevant E8 subgroup scheme
or nonabelian-cohomology exact sequence. The fields leftNeutrality and
rightNeutrality are the two Type-D Serre-II providers, while
lift_of_correctable is the central lifting theorem still missing in the
geometric application. -/
structure D4PairCentralReduction {X : Type x} (point neutral : X) where
  QuotientH1 : Type u
  LeftH1 : Type u
  RightH1 : Type u
  Obstruction : Type u
  Correction : Type u
  [obstructionAddCommGroup : AddCommGroup Obstruction]
  quotientNeutral : QuotientH1
  leftNeutral : LeftH1
  rightNeutral : RightH1
  reduced : QuotientH1
  induce : QuotientH1 → X
  induce_neutral : induce quotientNeutral = neutral
  realizes : induce reduced = point
  descendPair : LeftH1 × RightH1 → QuotientH1
  descendPair_neutral :
    descendPair (leftNeutral, rightNeutral) = quotientNeutral
  leftNeutrality : ∀ η : LeftH1, η = leftNeutral
  rightNeutrality : ∀ η : RightH1, η = rightNeutral
  obstruction : QuotientH1 → Obstruction
  correctionBoundary : Correction → Obstruction
  lift_of_correctable :
    ∀ η : QuotientH1,
      (∃ c, correctionBoundary c = obstruction η) →
        ∃ ζ : LeftH1 × RightH1, descendPair ζ = η

namespace D4PairCentralReduction

/-- The trialitarian correction package: the central residue is two-torsion
and its cubic multiple lies in the correction-boundary image. -/
def HasTrialitarianCorrection
    {X : Type x} {point neutral : X}
    (P : D4PairCentralReduction.{u, x} point neutral) : Prop :=
  let _ : AddCommGroup P.Obstruction := P.obstructionAddCommGroup
  (2 : ℕ) • P.obstruction P.reduced = 0 ∧
    ∃ c, P.correctionBoundary c =
      (3 : ℕ) • P.obstruction P.reduced

/-- A cubic correction of a two-primary central residue lifts the reduced
class to two neutral Type-D classes, hence neutralizes the original class.

This is a conditional research reduction: every field-valued group-scheme
and central-lifting input is visible in D4PairCentralReduction. -/
theorem eq_neutral_of_trialitarianCorrection
    {X : Type x} {point neutral : X}
    (P : D4PairCentralReduction.{u, x} point neutral)
    (h : P.HasTrialitarianCorrection) :
    point = neutral := by
  let _ : AddCommGroup P.Obstruction := P.obstructionAddCommGroup
  rcases h with ⟨h2, hcubic⟩
  have hcorrectable :
      ∃ c, P.correctionBoundary c = P.obstruction P.reduced :=
    central_residue_of_cubic_norm P.correctionBoundary h2 hcubic
  obtain ⟨ζ, hζ⟩ := P.lift_of_correctable P.reduced hcorrectable
  have hpair : ζ = (P.leftNeutral, P.rightNeutral) := by
    apply Prod.ext
    · simpa using P.leftNeutrality ζ.1
    · simpa using P.rightNeutrality ζ.2
  calc
    point = P.induce P.reduced := P.realizes.symm
    _ = P.induce (P.descendPair ζ) := congrArg P.induce hζ.symm
    _ = P.induce
        (P.descendPair (P.leftNeutral, P.rightNeutral)) := by
      rw [hpair]
    _ = P.induce P.quotientNeutral :=
      congrArg P.induce P.descendPair_neutral
    _ = neutral := P.induce_neutral

/-- Contrapositive form: a nonneutral reduced class cannot have the
trialitarian cubic correction package. -/
theorem not_hasTrialitarianCorrection_of_ne
    {X : Type x} {point neutral : X}
    (P : D4PairCentralReduction.{u, x} point neutral)
    (hneutral : point ≠ neutral) :
    ¬ P.HasTrialitarianCorrection := by
  intro h
  exact hneutral (P.eq_neutral_of_trialitarianCorrection h)

end D4PairCentralReduction

/-- The projective-order-60 part of the aligned perfect-core lift certificate:
the binary-icosahedral survivor packet. -/
abbrev E8PerfectCoreSurvivorCase.IsBinaryIcosahedral
    (survivor : E8PerfectCoreSurvivorCase) : Prop :=
  survivor.datum.projectiveOrder = 60

/-- The binary-icosahedral packet consists exactly of the four displayed
aligned table classes. This is a finite certificate statement and does not
identify the countercertified inner D4-by-D4 orbit with one of 4015 or 4017.
-/
theorem E8PerfectCoreSurvivorCase.isBinaryIcosahedral_iff_tableClass
    (survivor : E8PerfectCoreSurvivorCase) :
    survivor.IsBinaryIcosahedral ↔
      survivor.datum.tableClass = 4013 ∨
      survivor.datum.tableClass = 4014 ∨
      survivor.datum.tableClass = 4015 ∨
      survivor.datum.tableClass = 4017 := by
  set_option maxRecDepth 10000 in
    decide +revert

/-- Exactly four rows in the aligned lift certificate belong to the
binary-icosahedral packet. -/
theorem E8PerfectCoreSurvivorCase.binaryIcosahedral_row_count :
    (RiemannResearch.E8.omegaEightPlusTwoPerfectCoreLiftData.filter
      (fun row => row.projectiveOrder = 60)).length = 4 := by
  decide

/-- The complement of the binary-icosahedral packet has twenty-seven rows. -/
theorem E8PerfectCoreSurvivorCase.nonBinaryIcosahedral_row_count :
    (RiemannResearch.E8.omegaEightPlusTwoPerfectCoreLiftData.filter
      (fun row => row.projectiveOrder ≠ 60)).length = 27 := by
  decide

namespace E8SurvivorReductionData

/-- Split the 31-survivor completion into twenty-seven residual common-gauge
cases and four binary-icosahedral cases handled by trialitarian D4-pair
central reductions.

Compared with eq_neutral_of_commonGauges, this removes the common-gauge
hypothesis on the four binary rows. It replaces it by the explicit and
strictly narrower D4-pair obligations packaged by
D4PairCentralReduction.HasTrialitarianCorrection. -/
theorem
    eq_neutral_of_nonbinaryCommonGauges_and_binaryTrialitarianReductions
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral)
    (nonbinaryCommonGauge :
      ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
        (_h : D.realizes ξ survivor),
        ¬ survivor.IsBinaryIcosahedral →
          (D.reduction ξ survivor _h).HasCommonGauge)
    (binaryReduction :
      ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
        (_h : D.realizes ξ survivor),
        survivor.IsBinaryIcosahedral →
          ∃ P : D4PairCentralReduction.{u, x} ξ neutral,
            P.HasTrialitarianCorrection)
    (ξ : X) :
    ξ = neutral := by
  rcases D.classify ξ with hInduced | hSurvivor
  · obtain ⟨s, η, hη⟩ := hInduced
    exact
      hη ▸ D.induction.induced_eq_neutral
        D.allSubsystemsSerreII s η
  · obtain ⟨survivor, hrealizes⟩ := hSurvivor
    by_cases hs : survivor.IsBinaryIcosahedral
    · obtain ⟨P, hP⟩ :=
        binaryReduction ξ survivor hrealizes hs
      exact P.eq_neutral_of_trialitarianCorrection hP
    · exact
        (D.reduction ξ survivor hrealizes).eq_basepoint_of_commonGauge
          (nonbinaryCommonGauge ξ survivor hrealizes hs)

end E8SurvivorReductionData

/-- Exact E8 family provider in which only the twenty-seven nonbinary
survivors require common gauges. The four binary-icosahedral survivors are
instead discharged by supplied trialitarian D4-pair central reductions. -/
theorem
    exactFamilyE8_of_nonbinaryCommonGauges_and_binaryTrialitarianReductions
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (reductions :
      ∀ (R A : CommRingCat.{x}) [HopfAlgebra R A],
        Base R →
        GroupCondition R A →
        family R A = .E8 →
          E8SurvivorReductionData.{u, x + 1} (FpqcH1.neutral R A))
    (nonbinaryCommonGauge :
      ∀ (R A : CommRingCat.{x}) [HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8)
        (ξ : FpqcH1.{x, x} R A)
        (survivor : E8PerfectCoreSurvivorCase)
        (_h :
          (reductions R A hBase hGroup hE8).realizes ξ survivor),
        ¬ survivor.IsBinaryIcosahedral →
          ((reductions R A hBase hGroup hE8).reduction
            ξ survivor _h).HasCommonGauge)
    (binaryReduction :
      ∀ (R A : CommRingCat.{x}) [HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8)
        (ξ : FpqcH1.{x, x} R A)
        (survivor : E8PerfectCoreSurvivorCase)
        (_h :
          (reductions R A hBase hGroup hE8).realizes ξ survivor),
        survivor.IsBinaryIcosahedral →
          ∃ P : D4PairCentralReduction.{u, x + 1}
              ξ (FpqcH1.neutral R A),
            P.HasTrialitarianCorrection) :
    ExactFamilyNeutralityProvider Base GroupCondition family .E8 := by
  intro R A _ hBase hGroup hE8
  let D := reductions R A hBase hGroup hE8
  have hnonbinary :
      ∀ (ξ : FpqcH1.{x, x} R A)
        (survivor : E8PerfectCoreSurvivorCase)
        (_h : D.realizes ξ survivor),
        ¬ survivor.IsBinaryIcosahedral →
          (D.reduction ξ survivor _h).HasCommonGauge := by
    intro ξ survivor hrealizes hs
    simpa [D] using
      nonbinaryCommonGauge R A hBase hGroup hE8
        ξ survivor hrealizes hs
  have hbinary :
      ∀ (ξ : FpqcH1.{x, x} R A)
        (survivor : E8PerfectCoreSurvivorCase)
        (_h : D.realizes ξ survivor),
        survivor.IsBinaryIcosahedral →
          ∃ P : D4PairCentralReduction.{u, x + 1}
              ξ (FpqcH1.neutral R A),
            P.HasTrialitarianCorrection := by
    intro ξ survivor hrealizes hs
    simpa [D] using
      binaryReduction R A hBase hGroup hE8
        ξ survivor hrealizes hs
  constructor
  intro ξ η
  exact
    (D.eq_neutral_of_nonbinaryCommonGauges_and_binaryTrialitarianReductions
      hnonbinary hbinary ξ).trans
    (D.eq_neutral_of_nonbinaryCommonGauges_and_binaryTrialitarianReductions
      hnonbinary hbinary η).symm

/-- Terminal family-hierarchy reduction for full Serre II. It leaves the
finite-Galois/fpqc realization, the twenty-seven residual common gauges, and
the four trialitarian D4-pair central reductions as explicit hypotheses. -/
theorem serreII_of_familyHierarchy_and_binaryTrialitarianReductions
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (hierarchy :
      NonE8FamilyNeutralityHierarchy Base GroupCondition family)
    (reductions :
      ∀ (R A : CommRingCat.{x}) [HopfAlgebra R A],
        Base R →
        GroupCondition R A →
        family R A = .E8 →
          E8SurvivorReductionData.{u, x + 1} (FpqcH1.neutral R A))
    (nonbinaryCommonGauge :
      ∀ (R A : CommRingCat.{x}) [HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8)
        (ξ : FpqcH1.{x, x} R A)
        (survivor : E8PerfectCoreSurvivorCase)
        (_h :
          (reductions R A hBase hGroup hE8).realizes ξ survivor),
        ¬ survivor.IsBinaryIcosahedral →
          ((reductions R A hBase hGroup hE8).reduction
            ξ survivor _h).HasCommonGauge)
    (binaryReduction :
      ∀ (R A : CommRingCat.{x}) [HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8)
        (ξ : FpqcH1.{x, x} R A)
        (survivor : E8PerfectCoreSurvivorCase)
        (_h :
          (reductions R A hBase hGroup hE8).realizes ξ survivor),
        survivor.IsBinaryIcosahedral →
          ∃ P : D4PairCentralReduction.{u, x + 1}
              ξ (FpqcH1.neutral R A),
            P.HasTrialitarianCorrection) :
    Conjecture Base GroupCondition :=
  hierarchy.conjecture_of_e8
    (exactFamilyE8_of_nonbinaryCommonGauges_and_binaryTrialitarianReductions
      Base GroupCondition family reductions
      nonbinaryCommonGauge binaryReduction)


end RiemannResearch.AlgebraicGeometry.SerreII
