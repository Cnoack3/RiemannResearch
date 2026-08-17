/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIIE8Completion
import RiemannResearch.E8.BinaryIcosahedralSubsystemOrbits
import RiemannResearch.GroupCohomology.TrialitarianCentralResidue

/-!
# Orbitwise D4-pair reduction for the binary E8 survivors

This module gives an honest conditional interface for the orbitwise
D4 × D4 route to the four binary-icosahedral E8 survivor rows.

The finite certificate proves that table classes 4013, 4014, 4015, and 4017
all have at least one degree-five (D4)^2 subsystem orbit. A completion
provider must then supply one fixed D4-pair central geometry for the whole
pointed set, choose a certified orbit for every realized binary survivor,
classify its diagram action as inner or cyclic cubic, and prove the
corresponding lifting condition.

The distinction between fixed geometry and pointwise orbit reduction is
essential. If the quotient types and maps are allowed to vary with the point,
then the old existential reduction package can be manufactured precisely when
the desired conclusion point = neutral is already known. It therefore does
not constitute a genuine reduction.

For an inner orbit, the required condition is vanishing of the central
obstruction and a supplied zero-obstruction lifting theorem. For a cyclic
cubic orbit, it is the two-torsion/cubic-boundary package; the arithmetic fact
that 3 • z = z for two-torsion z converts it into a correctable boundary.

This module does not construct Spin₈, the central quotient
(Spin₈ × Spin₈) / μ₂², its embedding in E8, the torsor reduction, the
connecting H2 obstruction, the eleven unresolved diagram actions, or the
orbit-specific cubic boundary theorem.

Sources:

* User-provided handoff, From the D4 Discriminant–Triality Theorem to
  Serre II for E8; this supports the reduction architecture.
* Skip Garibaldi, E8, the most exceptional group,
  <https://www.garibaldibros.com/linked-files/e8.pdf>; this supports the
  D4-by-D4 central-quotient architecture, not the torsor reductions supplied
  here as explicit data.
-/

universe u x

namespace RiemannResearch.AlgebraicGeometry.SerreII

open RiemannResearch.E8
open RiemannResearch.GroupCohomology

/-- A single fixed central-quotient geometry for all point classes under
consideration.

This is an interface, not a construction of the relevant E8 subgroup scheme
or nonabelian-cohomology exact sequence. The two neutrality fields are the
Type-D Serre-II inputs. The two lifting fields distinguish the classical
inner-orbit branch from the cyclic-cubic triality branch. -/
structure D4PairCentralGeometry (X : Type x) (neutral : X) where
  QuotientH1 : Type u
  LeftH1 : Type u
  RightH1 : Type u
  Obstruction : Type u
  Correction : Type u
  [obstructionAddCommGroup : AddCommGroup Obstruction]
  quotientNeutral : QuotientH1
  leftNeutral : LeftH1
  rightNeutral : RightH1
  induce : QuotientH1 → X
  induce_neutral : induce quotientNeutral = neutral
  descendPair : LeftH1 × RightH1 → QuotientH1
  descendPair_neutral :
    descendPair (leftNeutral, rightNeutral) = quotientNeutral
  leftNeutrality : ∀ η : LeftH1, η = leftNeutral
  rightNeutrality : ∀ η : RightH1, η = rightNeutral
  obstruction : QuotientH1 → Obstruction
  correctionBoundary : Correction → Obstruction
  lift_of_zero :
    ∀ η : QuotientH1, obstruction η = 0 →
      ∃ ζ : LeftH1 × RightH1, descendPair ζ = η
  lift_of_correctable :
    ∀ η : QuotientH1,
      (∃ c, correctionBoundary c = obstruction η) →
        ∃ ζ : LeftH1 × RightH1, descendPair ζ = η

/-- The two orbitwise diagram-action branches allowed by the corrected
degree-five (D4)^2 analysis. -/
inductive BinaryD4OrbitAction where
  | inner
  | cyclicCubic
  deriving DecidableEq, Repr

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
    (omegaEightPlusTwoPerfectCoreLiftData.filter
      (fun row => row.projectiveOrder ≠ 60)).length = 27 := by
  decide

/-- A concrete orbit in the compressed finite certificate: the table row
matches the survivor and the Fin index selects one of its degree-five
(D4)^2 orbits. -/
structure CertifiedDegreeFiveD4Orbit
    (survivor : E8PerfectCoreSurvivorCase) where
  datum : A5SubsystemOrbitDatum
  datum_mem : datum ∈ binaryIcosahedralSubsystemOrbitData
  tableClass_eq : datum.tableClass = survivor.datum.tableClass
  orbitIndex :
    Fin (orbitDegreeMultiplicity 5 datum.d4d4OrbitHistogram)

/-- Every binary-icosahedral survivor row has a certified degree-five
(D4)^2 orbit. This is the exact finite consequence of the committed
histograms; it makes no assertion about the orbit's diagram action. -/
theorem E8PerfectCoreSurvivorCase.exists_certifiedDegreeFiveD4Orbit
    (survivor : E8PerfectCoreSurvivorCase)
    (h : survivor.IsBinaryIcosahedral) :
    Nonempty (CertifiedDegreeFiveD4Orbit survivor) := by
  rw [E8PerfectCoreSurvivorCase.isBinaryIcosahedral_iff_tableClass] at h
  rcases h with h | h | h | h
  · refine
      ⟨⟨binaryIcosahedralSubsystemOrbitData[0], by decide, ?_,
        ⟨0, by decide⟩⟩⟩
    simpa [binaryIcosahedralSubsystemOrbitData] using h.symm
  · refine
      ⟨⟨binaryIcosahedralSubsystemOrbitData[1], by decide, ?_,
        ⟨0, by decide⟩⟩⟩
    simpa [binaryIcosahedralSubsystemOrbitData] using h.symm
  · refine
      ⟨⟨binaryIcosahedralSubsystemOrbitData[2], by decide, ?_,
        ⟨0, by decide⟩⟩⟩
    simpa [binaryIcosahedralSubsystemOrbitData] using h.symm
  · refine
      ⟨⟨binaryIcosahedralSubsystemOrbitData[3], by decide, ?_,
        ⟨0, by decide⟩⟩⟩
    simpa [binaryIcosahedralSubsystemOrbitData] using h.symm

/-- The pointwise data attached to one actual certified degree-five orbit
inside a fixed D4-pair geometry. Unlike the removed interface, this structure
does not choose its own quotient types or induction map. -/
structure BinaryD4OrbitReduction
    {X : Type x} {neutral : X}
    (G : D4PairCentralGeometry.{u, x} X neutral)
    (point : X) (survivor : E8PerfectCoreSurvivorCase) where
  orbit : CertifiedDegreeFiveD4Orbit survivor
  reduced : G.QuotientH1
  realizes : G.induce reduced = point
  action : BinaryD4OrbitAction

namespace BinaryD4OrbitReduction

/-- The correction required by the actual diagram-action branch.

An inner orbit requires zero central obstruction. A cyclic-cubic orbit
requires a two-torsion residue whose cubic multiple lies in the
correction-boundary image. -/
def HasRequiredCorrection
    {X : Type x} {neutral : X}
    {G : D4PairCentralGeometry.{u, x} X neutral}
    {point : X} {survivor : E8PerfectCoreSurvivorCase}
    (P : BinaryD4OrbitReduction G point survivor) : Prop :=
  let _ : AddCommGroup G.Obstruction := G.obstructionAddCommGroup
  match P.action with
  | .inner => G.obstruction P.reduced = 0
  | .cyclicCubic =>
      (2 : ℕ) • G.obstruction P.reduced = 0 ∧
        ∃ c, G.correctionBoundary c =
          (3 : ℕ) • G.obstruction P.reduced

/-- An orbitwise correction lifts the reduced class to two neutral Type-D
classes, hence neutralizes the original class. -/
theorem eq_neutral_of_requiredCorrection
    {X : Type x} {neutral : X}
    {G : D4PairCentralGeometry.{u, x} X neutral}
    {point : X} {survivor : E8PerfectCoreSurvivorCase}
    (P : BinaryD4OrbitReduction G point survivor)
    (h : P.HasRequiredCorrection) :
    point = neutral := by
  let _ : AddCommGroup G.Obstruction := G.obstructionAddCommGroup
  have hlift :
      ∃ ζ : G.LeftH1 × G.RightH1,
        G.descendPair ζ = P.reduced := by
    cases ha : P.action with
    | inner =>
        rw [HasRequiredCorrection, ha] at h
        exact G.lift_of_zero P.reduced h
    | cyclicCubic =>
        rw [HasRequiredCorrection, ha] at h
        rcases h with ⟨h2, hcubic⟩
        exact G.lift_of_correctable P.reduced
          (central_residue_of_cubic_norm
            G.correctionBoundary h2 hcubic)
  obtain ⟨ζ, hζ⟩ := hlift
  have hpair : ζ = (G.leftNeutral, G.rightNeutral) := by
    apply Prod.ext
    · simpa using G.leftNeutrality ζ.1
    · simpa using G.rightNeutrality ζ.2
  calc
    point = G.induce P.reduced := P.realizes.symm
    _ = G.induce (G.descendPair ζ) :=
      congrArg G.induce hζ.symm
    _ = G.induce
        (G.descendPair (G.leftNeutral, G.rightNeutral)) := by
      rw [hpair]
    _ = G.induce G.quotientNeutral :=
      congrArg G.induce G.descendPair_neutral
    _ = neutral := G.induce_neutral

/-- Contrapositive form relative to an explicitly supplied fixed geometry
and certified orbit reduction. -/
theorem not_hasRequiredCorrection_of_ne
    {X : Type x} {neutral : X}
    {G : D4PairCentralGeometry.{u, x} X neutral}
    {point : X} {survivor : E8PerfectCoreSurvivorCase}
    (P : BinaryD4OrbitReduction G point survivor)
    (hneutral : point ≠ neutral) :
    ¬ P.HasRequiredCorrection := by
  intro h
  exact hneutral (P.eq_neutral_of_requiredCorrection h)

end BinaryD4OrbitReduction

/-- A single fixed D4-pair geometry together with orbitwise reductions and
corrections for every realized binary survivor.

The geometry is chosen once for D; only the certified orbit, reduced class,
and action branch vary with the point. This prevents pointwise manufacture of
the entire reduction interface from the desired neutrality equality. -/
structure BinaryD4OrbitProvider
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral) where
  geometry : D4PairCentralGeometry.{u, x} X neutral
  reduction :
    ∀ (point : X) (survivor : E8PerfectCoreSurvivorCase)
      (_h : D.realizes point survivor),
      survivor.IsBinaryIcosahedral →
        BinaryD4OrbitReduction geometry point survivor
  correction :
    ∀ (point : X) (survivor : E8PerfectCoreSurvivorCase)
      (_h : D.realizes point survivor)
      (hbinary : survivor.IsBinaryIcosahedral),
      (reduction point survivor _h hbinary).HasRequiredCorrection

namespace E8SurvivorReductionData

/-- Split the 31-survivor completion into twenty-seven residual common-gauge
cases and four binary-icosahedral cases handled by a fixed geometry and
orbitwise D4-pair reductions.

The finite certificate supplies only the degree-five orbit witnesses. The
provider still has to realize every binary class in the fixed geometry,
classify the chosen orbit's actual action, and prove the matching correction.
-/
theorem
    eq_neutral_of_nonbinaryCommonGauges_and_binaryOrbitwiseD4Reductions
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral)
    (nonbinaryCommonGauge :
      ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
        (_h : D.realizes ξ survivor),
        ¬ survivor.IsBinaryIcosahedral →
          (D.reduction ξ survivor _h).HasCommonGauge)
    (binary : BinaryD4OrbitProvider D)
    (ξ : X) :
    ξ = neutral := by
  rcases D.classify ξ with hInduced | hSurvivor
  · obtain ⟨s, η, hη⟩ := hInduced
    exact
      hη ▸ D.induction.induced_eq_neutral
        D.allSubsystemsSerreII s η
  · obtain ⟨survivor, hrealizes⟩ := hSurvivor
    by_cases hs : survivor.IsBinaryIcosahedral
    · let P := binary.reduction ξ survivor hrealizes hs
      exact P.eq_neutral_of_requiredCorrection
        (binary.correction ξ survivor hrealizes hs)
    · exact
        (D.reduction ξ survivor hrealizes).eq_basepoint_of_commonGauge
          (nonbinaryCommonGauge ξ survivor hrealizes hs)

end E8SurvivorReductionData

/-- Exact E8 family provider in which only the twenty-seven nonbinary
survivors require common gauges. The four binary survivors are discharged by
a fixed-geometry, orbitwise D4-pair provider for each field and group. -/
theorem
    exactFamilyE8_of_nonbinaryCommonGauges_and_binaryOrbitwiseD4Reductions
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
          BinaryD4OrbitProvider
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
  let B : BinaryD4OrbitProvider D := by
    simpa [D] using binary R A hBase hGroup hE8
  constructor
  intro ξ η
  exact
    (D.eq_neutral_of_nonbinaryCommonGauges_and_binaryOrbitwiseD4Reductions
      hnonbinary B ξ).trans
    (D.eq_neutral_of_nonbinaryCommonGauges_and_binaryOrbitwiseD4Reductions
      hnonbinary B η).symm

/-- Terminal family-hierarchy reduction for full Serre II. It leaves the
finite-Galois realization, the twenty-seven residual common gauges, and
the fixed-geometry orbitwise D4-pair provider as explicit hypotheses. -/
theorem serreII_of_familyHierarchy_and_binaryOrbitwiseD4Reductions
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
          BinaryD4OrbitProvider
            (reductions R A hBase hGroup hE8)) :
    Conjecture Base GroupCondition :=
  hierarchy.conjecture_of_e8
    (exactFamilyE8_of_nonbinaryCommonGauges_and_binaryOrbitwiseD4Reductions
      Base GroupCondition family reductions
      nonbinaryCommonGauge binary)


end RiemannResearch.AlgebraicGeometry.SerreII
