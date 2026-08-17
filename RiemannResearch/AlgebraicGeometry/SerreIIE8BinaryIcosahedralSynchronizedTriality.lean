/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIIE8BinaryIcosahedralTwoField
import RiemannResearch.E8.D4PairEuclideanSimpleRoots

/-!
# Synchronized D4-by-D4 triality in the binary-icosahedral E8 reduction

The identity discriminant graph is the glue used by the explicit
D4-by-D4 construction of the E8 root datum. A pair of diagram actions
preserves this graph exactly when its two S3 components agree. Thus the
correct triality input is diagonal, or synchronized, triality rather than an
independent outer action on either D4 factor.

This module feeds that finite statement into the binary-icosahedral two-field
reduction. For every admissible transporter transition it records the two
diagram actions and their synchronization. The checked discriminant theorem
then supplies preservation of the E8 identity glue.

One substantive bridge remains explicit:
identity-glue preservation must imply factorization of the transporter
transition into a binary-tetrahedral fixed correction and a binary-dihedral
fixed correction. This is a group-scheme/transporter theorem; it does not
follow from the finite lattice calculation alone.

Source: user-provided synchronized D4-squared triality proposal, combined with
the existing identity-graph E8 root-data certificate.
-/

universe u x

namespace RiemannResearch.AlgebraicGeometry.SerreII

open RiemannResearch.Logic
open RiemannResearch.GaloisCohomology
open RiemannResearch.E8.BinaryIcosahedralSubgroups
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality

/-- Synchronized D4-by-D4 triality data for the transition between the two
local gauges.

The synchronization field is completely finite. The final field is the
remaining E8-specific lift from preservation of the identity discriminant
graph to the fixed-factor decomposition required by two-gauge descent. -/
structure SynchronizedD4PairTransitionFactorization
    {G : Type u} [Group G] [MulDistribMulAction SL2F5 G]
    (S6 S5 : Subgroup G) (theta : S6 ≃* S5) where
  leftTriality : G → DiagramSymmetry
  rightTriality : G → DiagramSymmetry
  synchronized :
    ∀ y : G,
      y ∈ orientedSubgroupTransporter S6 S5 theta →
        rightTriality y = leftTriality y
  factorizationOfGluePreservation :
    ∀ y : G,
      IsAdmissibleTwoGaugeTransition
        binaryTetrahedralSubgroup binaryDihedralSubgroup y →
      y ∈ orientedSubgroupTransporter S6 S5 theta →
      (∀ q, q ∈ discriminantGraph 1 →
        pairDiscriminantAction (leftTriality y) (rightTriality y) q ∈
          discriminantGraph 1) →
      ∃ a b : G,
        NonabelianCocycle.IsFixedBy binaryTetrahedralSubgroup a ∧
        NonabelianCocycle.IsFixedBy binaryDihedralSubgroup b ∧
        y = a * b

namespace SynchronizedD4PairTransitionFactorization

/-- Synchronization forces preservation of the diagonal D4-pair glue, so the
remaining glue-preservation bridge supplies the two fixed factors. -/
theorem factorization
    {G : Type u} [Group G] [MulDistribMulAction SL2F5 G]
    {S6 S5 : Subgroup G} {theta : S6 ≃* S5}
    (T : SynchronizedD4PairTransitionFactorization S6 S5 theta)
    (y : G)
    (hadmissible :
      IsAdmissibleTwoGaugeTransition
        binaryTetrahedralSubgroup binaryDihedralSubgroup y)
    (htransport :
      y ∈ orientedSubgroupTransporter S6 S5 theta) :
    ∃ a b : G,
      NonabelianCocycle.IsFixedBy binaryTetrahedralSubgroup a ∧
      NonabelianCocycle.IsFixedBy binaryDihedralSubgroup b ∧
      y = a * b := by
  apply T.factorizationOfGluePreservation y hadmissible htransport
  exact
    (pairAction_preserves_identityGraph_iff_synchronized
      (T.leftTriality y) (T.rightTriality y)).2
      (T.synchronized y htransport)

end SynchronizedD4PairTransitionFactorization

/-- Binary-icosahedral two-field data in which the transition factorization
is obtained from synchronized D4-by-D4 triality.

The Gille fields produce the two local gauges. The synchronized transition
data preserves the identity E8 glue and exposes only the final
glue-preservation-to-factorization bridge. -/
structure BinaryIcosahedralSynchronizedD4PairTwoFieldPresentation
    {X : Type x} (point neutral : X) where
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
  synchronizedTriality :
    SynchronizedD4PairTransitionFactorization S6 S5 theta
  reflectsNeutrality : cocycle.IsCoboundary → point = neutral

namespace BinaryIcosahedralSynchronizedD4PairTwoFieldPresentation

/-- Forget the geometric source of transition factorization and obtain the
binary-icosahedral Gille two-field presentation. -/
def toGilleTwoFieldPresentation
    {X : Type x} {point neutral : X}
    (P :
      BinaryIcosahedralSynchronizedD4PairTwoFieldPresentation.{u, x}
        point neutral) :
    BinaryIcosahedralGilleTwoFieldPresentation.{u, x} point neutral := by
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
    factorization := P.synchronizedTriality.factorization
    reflectsNeutrality := P.reflectsNeutrality
  }

/-- The synchronized D4-pair triality two-field reduction neutralizes the
realized E8 class. -/
theorem eq_basepoint
    {X : Type x} {point neutral : X}
    (P :
      BinaryIcosahedralSynchronizedD4PairTwoFieldPresentation.{u, x}
        point neutral) :
    point = neutral :=
  P.toGilleTwoFieldPresentation.eq_basepoint

end BinaryIcosahedralSynchronizedD4PairTwoFieldPresentation

/-- A synchronized D4-pair two-field presentation for every realized
binary-icosahedral survivor row. -/
structure BinaryIcosahedralSynchronizedD4PairTwoFieldProvider
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral) where
  presentation :
    ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
      (_h : D.realizes ξ survivor),
      survivor.IsBinaryIcosahedral →
        BinaryIcosahedralSynchronizedD4PairTwoFieldPresentation.{u, x}
          ξ neutral

namespace BinaryIcosahedralSynchronizedD4PairTwoFieldProvider

/-- A synchronized D4-pair provider supplies the transition factorization
required by the earlier Gille two-field provider. -/
def toGilleTwoFieldProvider
    {X : Type x} {neutral : X}
    {D : E8SurvivorReductionData.{u, x} neutral}
    (B : BinaryIcosahedralSynchronizedD4PairTwoFieldProvider D) :
    BinaryIcosahedralGilleTwoFieldProvider D where
  presentation ξ survivor hrealizes hs :=
    (B.presentation ξ survivor hrealizes hs).toGilleTwoFieldPresentation

end BinaryIcosahedralSynchronizedD4PairTwoFieldProvider

namespace E8SurvivorReductionData

/-- The 4 + 27 assembly using synchronized D4-by-D4 triality for the four
binary-icosahedral rows. -/
theorem
    eq_neutral_of_nonbinaryCommonGauges_and_binaryIcosahedralSynchronizedD4Pair
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral)
    (nonbinaryCommonGauge :
      ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
        (_h : D.realizes ξ survivor),
        ¬ survivor.IsBinaryIcosahedral →
          (D.reduction ξ survivor _h).HasCommonGauge)
    (binary : BinaryIcosahedralSynchronizedD4PairTwoFieldProvider D)
    (ξ : X) :
    ξ = neutral :=
  D.eq_neutral_of_nonbinaryCommonGauges_and_binaryIcosahedralGilleTwoField
    nonbinaryCommonGauge binary.toGilleTwoFieldProvider ξ

end E8SurvivorReductionData

/-- Exact E8 family provider from synchronized D4-pair two-field
presentations for the four binary rows and common gauges for the other
twenty-seven rows. -/
theorem
    exactFamilyE8_of_nonbinaryCommonGauges_and_binaryIcosahedralSynchronizedD4Pair
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
          BinaryIcosahedralSynchronizedD4PairTwoFieldProvider
            (reductions R A hBase hGroup hE8)) :
    ExactFamilyNeutralityProvider Base GroupCondition family .E8 :=
  exactFamilyE8_of_nonbinaryCommonGauges_and_binaryIcosahedralGilleTwoField
    Base GroupCondition family reductions nonbinaryCommonGauge
      (fun R A _ _ _ hBase hGroup hE8 =>
        (binary R A hBase hGroup hE8).toGilleTwoFieldProvider)

/-- Terminal family-hierarchy reduction using synchronized D4-by-D4 triality
inside the binary-icosahedral two-field argument. -/
theorem
    serreII_of_familyHierarchy_and_binaryIcosahedralSynchronizedD4Pair
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
          BinaryIcosahedralSynchronizedD4PairTwoFieldProvider
            (reductions R A hBase hGroup hE8)) :
    Conjecture Base GroupCondition :=
  hierarchy.conjecture_of_e8
    (exactFamilyE8_of_nonbinaryCommonGauges_and_binaryIcosahedralSynchronizedD4Pair
      Base GroupCondition family reductions nonbinaryCommonGauge binary)

end RiemannResearch.AlgebraicGeometry.SerreII
