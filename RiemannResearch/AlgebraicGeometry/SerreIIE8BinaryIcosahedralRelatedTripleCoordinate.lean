/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateGaloisSynchronizedPair

/-!
# Binary-icosahedral E8 reduction from related-triple coordinates

This module consumes the effective synchronized D4 coordinate-pair endpoint
in the binary-icosahedral two-field reduction.  A presentation now records
the actual finite-Galois coordinate pair and its transporter realization.
The adapter from the preceding module supplies the synchronized transition
geometry, after which the established Gille two-field proof neutralizes the
class.

The resulting provider plugs directly into the 4 + 27 E8 assembly and the
terminal family-hierarchy theorem.  The theorem is still conditional on
constructing the E8 transporter realization, the two Gille kernels, the
survivor realization, and the twenty-seven nonbinary common gauges.
-/

namespace RiemannResearch.AlgebraicGeometry.SerreII

open RiemannResearch.Logic
open RiemannResearch.GaloisCohomology
open RiemannResearch.E8.BinaryIcosahedralSubgroups

universe u x

/-- A binary-icosahedral two-field presentation whose synchronized D4 pair is
an effective pair of descended related-triple coordinate group schemes. -/
structure BinaryIcosahedralRelatedTripleCoordinateTwoFieldPresentation
    {X : Type x} (point neutral : X) where
  K : Type u
  L : Type u
  [fieldK : Field K]
  [fieldL : Field L]
  [algebraKL : Algebra K L]
  [finiteDimensionalKL : FiniteDimensional K L]
  [isGaloisKL : IsGalois K L]
  coordinatePair :
    RelatedTripleCoordinateGaloisSynchronizedPairData K L
  G : Type u
  [groupG : Group G]
  [action : MulDistribMulAction SL2F5 G]
  cocycle : NonabelianCocycle SL2F5 G
  tetrahedralGilleKernel :
    HasTrivialKernel
      (NonabelianH1.neutral :
        NonabelianH1 binaryTetrahedralSubgroup G)
      (NonabelianH1.neutral :
        NonabelianH1 (⊥ : Subgroup binaryTetrahedralSubgroup) G)
      (NonabelianH1.restrict
        (⊥ : Subgroup binaryTetrahedralSubgroup))
  dihedralGilleKernel :
    HasTrivialKernel
      (NonabelianH1.neutral :
        NonabelianH1 binaryDihedralSubgroup G)
      (NonabelianH1.neutral :
        NonabelianH1 (⊥ : Subgroup binaryDihedralSubgroup) G)
      (NonabelianH1.restrict
        (⊥ : Subgroup binaryDihedralSubgroup))
  S6 : Subgroup G
  S5 : Subgroup G
  theta : S6 ≃* S5
  orientedTransition :
    ∀ (gH gK : G),
      (∀ σ : binaryTetrahedralSubgroup,
        cocycle σ.1 = gH⁻¹ * σ.1 • gH) →
      (∀ σ : binaryDihedralSubgroup,
        cocycle σ.1 = gK⁻¹ * σ.1 • gK) →
      gH * gK⁻¹ ∈ orientedSubgroupTransporter S6 S5 theta
  transporterRealization :
    RelatedTripleCoordinateGaloisSynchronizedPairTransporterRealization
      coordinatePair S6 S5 theta
  reflectsNeutrality : cocycle.IsCoboundary → point = neutral

namespace BinaryIcosahedralRelatedTripleCoordinateTwoFieldPresentation

/-- Forget the explicit related-triple coordinate source and obtain the
synchronized D4-pair presentation used by the existing two-field theorem. -/
def toSynchronizedD4PairTwoFieldPresentation
    {X : Type x} {point neutral : X}
    (P :
      BinaryIcosahedralRelatedTripleCoordinateTwoFieldPresentation.{u, x}
        point neutral) :
    BinaryIcosahedralSynchronizedD4PairTwoFieldPresentation.{u, x}
      point neutral := by
  let _ : Field P.K := P.fieldK
  let _ : Field P.L := P.fieldL
  let _ : Algebra P.K P.L := P.algebraKL
  let _ : FiniteDimensional P.K P.L := P.finiteDimensionalKL
  let _ : IsGalois P.K P.L := P.isGaloisKL
  let _ : Group P.G := P.groupG
  let _ : MulDistribMulAction SL2F5 P.G := P.action
  exact {
    G := P.G
    cocycle := P.cocycle
    tetrahedralGilleKernel := P.tetrahedralGilleKernel
    dihedralGilleKernel := P.dihedralGilleKernel
    S6 := P.S6
    S5 := P.S5
    theta := P.theta
    orientedTransition := P.orientedTransition
    synchronizedTriality :=
      P.transporterRealization.toTransitionGeometry
    reflectsNeutrality := P.reflectsNeutrality
  }

/-- Effective related-triple coordinate data and the transporter realization
neutralize the binary-icosahedral class. -/
theorem eq_basepoint
    {X : Type x} {point neutral : X}
    (P :
      BinaryIcosahedralRelatedTripleCoordinateTwoFieldPresentation.{u, x}
        point neutral) :
    point = neutral :=
  P.toSynchronizedD4PairTwoFieldPresentation.eq_basepoint

end BinaryIcosahedralRelatedTripleCoordinateTwoFieldPresentation

/-- A related-triple coordinate presentation for every realized member of the
four-row binary-icosahedral survivor packet. -/
structure BinaryIcosahedralRelatedTripleCoordinateTwoFieldProvider
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral) where
  presentation :
    ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
      (_h : D.realizes ξ survivor),
      survivor.IsBinaryIcosahedral →
        BinaryIcosahedralRelatedTripleCoordinateTwoFieldPresentation.{u, x}
          ξ neutral

namespace BinaryIcosahedralRelatedTripleCoordinateTwoFieldProvider

/-- A coordinate provider supplies the existing synchronized D4-pair
provider. -/
def toSynchronizedD4PairTwoFieldProvider
    {X : Type x} {neutral : X}
    {D : E8SurvivorReductionData.{u, x} neutral}
    (B : BinaryIcosahedralRelatedTripleCoordinateTwoFieldProvider D) :
    BinaryIcosahedralSynchronizedD4PairTwoFieldProvider D where
  presentation ξ survivor hrealizes hs :=
    (B.presentation ξ survivor hrealizes hs)
      |>.toSynchronizedD4PairTwoFieldPresentation

end BinaryIcosahedralRelatedTripleCoordinateTwoFieldProvider

namespace E8SurvivorReductionData

/-- The 4 + 27 E8 assembly with effective related-triple coordinate
presentations for the four binary rows. -/
theorem eq_neutral_of_nonbinaryCommonGauges_and_binaryRelatedTripleCoordinate
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral)
    (nonbinaryCommonGauge :
      ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
        (_h : D.realizes ξ survivor),
        ¬ survivor.IsBinaryIcosahedral →
          (D.reduction ξ survivor _h).HasCommonGauge)
    (binary : BinaryIcosahedralRelatedTripleCoordinateTwoFieldProvider D)
    (ξ : X) :
    ξ = neutral :=
  D.eq_neutral_of_nonbinaryCommonGauges_and_binaryIcosahedralSynchronizedD4Pair
    nonbinaryCommonGauge
    binary.toSynchronizedD4PairTwoFieldProvider ξ

end E8SurvivorReductionData

/-- Exact E8 family neutrality from related-triple coordinate presentations
for the four binary rows and common gauges for the other twenty-seven rows. -/
theorem exactFamilyE8_of_nonbinaryCommonGauges_and_binaryRelatedTripleCoordinate
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
          BinaryIcosahedralRelatedTripleCoordinateTwoFieldProvider
            (reductions R A hBase hGroup hE8)) :
    ExactFamilyNeutralityProvider Base GroupCondition family .E8 :=
  exactFamilyE8_of_nonbinaryCommonGauges_and_binaryIcosahedralSynchronizedD4Pair
    Base GroupCondition family reductions nonbinaryCommonGauge
      (fun R A _ _ _ hBase hGroup hE8 =>
        (binary R A hBase hGroup hE8).toSynchronizedD4PairTwoFieldProvider)

/-- Terminal Serre-II reduction using effective related-triple coordinate
presentations in the four binary-icosahedral E8 rows. -/
theorem serreII_of_familyHierarchy_and_binaryRelatedTripleCoordinate
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
          BinaryIcosahedralRelatedTripleCoordinateTwoFieldProvider
            (reductions R A hBase hGroup hE8)) :
    Conjecture Base GroupCondition :=
  hierarchy.conjecture_of_e8
    (exactFamilyE8_of_nonbinaryCommonGauges_and_binaryRelatedTripleCoordinate
      Base GroupCondition family reductions nonbinaryCommonGauge binary)

end RiemannResearch.AlgebraicGeometry.SerreII
