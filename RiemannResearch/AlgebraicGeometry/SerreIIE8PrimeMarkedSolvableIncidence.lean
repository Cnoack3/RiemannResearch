/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.SerreIIE8BinaryIcosahedralRelatedTripleCoordinate
import RiemannResearch.E8.PrimeMarkedSolvableIncidence

/-!
# Prime-marked solvable incidence for the nonbinary E8 rows

This module specializes the solvable-incidence completion boundary to the
three E8 orbit degrees 135, 11200, and 12096. The committed prime-marked
packet proves that these degrees have gcd one, so a certificate needs
finite-index and restriction data only at its three distinguished
stabilizers; it does not repeat a separate arithmetic gcd proof or impose
finite index on every member of the ambient generating family.

For the twenty-seven nonbinary survivor rows, a provider of these specialized
certificates supplies the common gauges required by the existing 4 + 27
assembly. Together with the effective related-triple coordinate provider for
the four binary-icosahedral rows, this reaches the terminal conditional
Serre-II reduction.

The certificate remains an honest geometric boundary. It does not construct
the common band-valued gauge, the three restriction vanishings, the correction
into the unipotent subgroup, or terminal unipotent H¹ vanishing.
-/

universe u v w x

namespace RiemannResearch.AlgebraicGeometry.SerreII

open RiemannResearch.GaloisCohomology
open RiemannResearch.GroupCohomology

/-- Solvable-incidence data at the three prime-marked E8 stabilizers.

The arithmetic step is not a field: it is discharged by the committed
135/11200/12096 restriction theorem. -/
structure PrimeMarkedSolvableFiltrationCertificate
    {k Γ : Type u} {G : Type v} {I : Type w}
    [CommRing k] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G) (S : I → Subgroup Γ) where
  B : Subgroup G
  U : Subgroup G
  T : Rep k Γ
  i2 : I
  i3 : I
  i5 : I
  finiteIndex2 : (S i2).FiniteIndex
  finiteIndex3 : (S i3).FiniteIndex
  finiteIndex5 : (S i5).FiniteIndex
  card2 : Nat.card (Γ ⧸ S i2) = 135
  card3 : Nat.card (Γ ⧸ S i3) = 11_200
  card5 : Nat.card (Γ ⧸ S i5) = 12_096
  bandGauge : G
  bandValued : (a.gauge bandGauge).ValuesIn B
  obstruction : groupCohomology.H1 T
  obstruction_local2 :
    h1RestrictionViaCocycles T (S i2) obstruction = 0
  obstruction_local3 :
    h1RestrictionViaCocycles T (S i3) obstruction = 0
  obstruction_local5 :
    h1RestrictionViaCocycles T (S i5) obstruction = 0
  correct_to_unipotent :
    obstruction = 0 →
      ∃ q : B, ((a.gauge bandGauge).gauge (q : G)).ValuesIn U
  unipotent_h1 :
    ∀ z : NonabelianCocycle Γ G, z.ValuesIn U → z.IsCoboundary

namespace PrimeMarkedSolvableFiltrationCertificate

/-- The prime-marked packet kills the residual additive obstruction and hence
neutralizes the original nonabelian cocycle. -/
theorem isCoboundary
    {k Γ : Type u} {G : Type v} {I : Type w}
    [CommRing k] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    {a : NonabelianCocycle Γ G} {S : I → Subgroup Γ}
    (C : PrimeMarkedSolvableFiltrationCertificate (k := k) a S) :
    a.IsCoboundary := by
  let _ : (S C.i2).FiniteIndex := C.finiteIndex2
  let _ : (S C.i3).FiniteIndex := C.finiteIndex3
  let _ : (S C.i5).FiniteIndex := C.finiteIndex5
  exact
    a.isCoboundary_of_primeMarked_solvableIncidence
      C.B C.U C.T (S C.i2) (S C.i3) (S C.i5)
      C.card2 C.card3 C.card5 C.bandGauge C.bandValued
      C.obstruction C.obstruction_local2 C.obstruction_local3
      C.obstruction_local5 C.correct_to_unipotent C.unipotent_h1

/-- The same packet-specialized calculation gives the anchored fixed
correction for any separately constructed generating family of local gauges. -/
theorem exists_anchoredFixedGaugeCorrection
    {k Γ : Type u} {G : Type v} {I : Type w}
    [CommRing k] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    {a : NonabelianCocycle Γ G} {S : I → Subgroup Γ}
    (C : PrimeMarkedSolvableFiltrationCertificate (k := k) a S)
    (localGauge : I → G) (anchor : I)
    (hgen : (⨆ i, S i) = ⊤)
    (hlocal : ∀ i, a.IsLocalGauge (S i) (localGauge i)) :
    ∃ c₀ : G, ∀ i,
      NonabelianCocycle.IsFixedBy (S i)
        (NonabelianCocycle.transition localGauge i anchor * c₀) := by
  let _ : (S C.i2).FiniteIndex := C.finiteIndex2
  let _ : (S C.i3).FiniteIndex := C.finiteIndex3
  let _ : (S C.i5).FiniteIndex := C.finiteIndex5
  exact
    a.exists_anchoredFixedGaugeCorrection_of_primeMarked_solvableIncidence
      C.B C.U C.T S C.i2 C.i3 C.i5 anchor
      C.card2 C.card3 C.card5 localGauge hgen hlocal
      C.bandGauge C.bandValued C.obstruction C.obstruction_local2
      C.obstruction_local3 C.obstruction_local5 C.correct_to_unipotent
      C.unipotent_h1

end PrimeMarkedSolvableFiltrationCertificate

namespace AnchoredGaugeReduction

/-- A prime-marked solvable-incidence certificate attached to one anchored
E8 survivor reduction. -/
structure PrimeMarkedSolvableIncidenceCertificate
    {X : Type x} {point basepoint : X}
    (P : AnchoredGaugeReduction.{u, x} point basepoint) where
  k : Type u
  commRingK : CommRing k
  core :
    let _ : CommRing k := commRingK
    let _ : Group P.Γ := P.groupΓ
    let _ : Group P.G := P.groupG
    let _ : MulDistribMulAction P.Γ P.G := P.action
    PrimeMarkedSolvableFiltrationCertificate (k := k)
      P.cocycle P.stabilizer

/-- A prime-marked certificate supplies the common gauge required by the
survivor reduction. -/
theorem hasCommonGauge_of_primeMarkedSolvableIncidenceCertificate
    {X : Type x} {point basepoint : X}
    (P : AnchoredGaugeReduction.{u, x} point basepoint)
    (C : P.PrimeMarkedSolvableIncidenceCertificate) :
    P.HasCommonGauge := by
  let _ : CommRing C.k := C.commRingK
  let _ : Group P.Γ := P.groupΓ
  let _ : Group P.G := P.groupG
  let _ : MulDistribMulAction P.Γ P.G := P.action
  apply (P.hasCommonGauge_iff_hasAnchoredFixedCorrection).2
  exact C.core.exists_anchoredFixedGaugeCorrection
    P.gauge P.anchor P.generates P.localGauge

end AnchoredGaugeReduction

/-- Prime-marked solvable-incidence certificates for every realized
nonbinary survivor row. -/
structure NonbinaryPrimeMarkedSolvableIncidenceProvider
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral) where
  certificate :
    ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
      (h : D.realizes ξ survivor),
      ¬ survivor.IsBinaryIcosahedral →
        (D.reduction ξ survivor h).PrimeMarkedSolvableIncidenceCertificate

namespace NonbinaryPrimeMarkedSolvableIncidenceProvider

/-- The provider exposes the common-gauge interface used by the 4 + 27
assembly. -/
theorem hasCommonGauge
    {X : Type x} {neutral : X}
    {D : E8SurvivorReductionData.{u, x} neutral}
    (N : NonbinaryPrimeMarkedSolvableIncidenceProvider D)
    (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
    (h : D.realizes ξ survivor)
    (hs : ¬ survivor.IsBinaryIcosahedral) :
    (D.reduction ξ survivor h).HasCommonGauge :=
  (D.reduction ξ survivor h)
    |>.hasCommonGauge_of_primeMarkedSolvableIncidenceCertificate
      (N.certificate ξ survivor h hs)

end NonbinaryPrimeMarkedSolvableIncidenceProvider

namespace E8SurvivorReductionData

/-- The sharpened 4 + 27 assembly: prime-marked solvable incidence handles
the twenty-seven nonbinary rows, while effective related-triple coordinates
handle the four binary-icosahedral rows. -/
theorem
    eq_neutral_of_nonbinaryPrimeMarkedSolvableIncidence_and_binaryRelatedTripleCoordinate
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral)
    (nonbinary : NonbinaryPrimeMarkedSolvableIncidenceProvider D)
    (binary : BinaryIcosahedralRelatedTripleCoordinateTwoFieldProvider D)
    (ξ : X) :
    ξ = neutral :=
  D.eq_neutral_of_nonbinaryCommonGauges_and_binaryRelatedTripleCoordinate
    nonbinary.hasCommonGauge binary ξ

end E8SurvivorReductionData

/-- Exact E8 family neutrality from prime-marked solvable-incidence
certificates on the twenty-seven nonbinary rows and effective related-triple
coordinates on the four binary rows. -/
theorem
    exactFamilyE8_of_nonbinaryPrimeMarkedSolvableIncidence_and_binaryRelatedTripleCoordinate
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (reductions :
      ∀ (R A : Type x) [Field R] [CommRing A] [HopfAlgebra R A],
        Base R →
        GroupCondition R A →
        family R A = .E8 →
          E8SurvivorReductionData.{u, x} (GaloisH1.neutral R A))
    (nonbinary :
      ∀ (R A : Type x) [Field R] [CommRing A] [HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8),
          NonbinaryPrimeMarkedSolvableIncidenceProvider
            (reductions R A hBase hGroup hE8))
    (binary :
      ∀ (R A : Type x) [Field R] [CommRing A] [HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8),
          BinaryIcosahedralRelatedTripleCoordinateTwoFieldProvider
            (reductions R A hBase hGroup hE8)) :
    ExactFamilyNeutralityProvider Base GroupCondition family .E8 :=
  exactFamilyE8_of_nonbinaryCommonGauges_and_binaryRelatedTripleCoordinate
    Base GroupCondition family reductions
      (fun R A _ _ _ hBase hGroup hE8 ξ survivor hrealizes hs =>
        (nonbinary R A hBase hGroup hE8).hasCommonGauge
          ξ survivor hrealizes hs)
      binary

/-- Terminal Serre-II reduction with the prime-marked arithmetic removed from
the twenty-seven nonbinary geometric obligations. -/
theorem
    serreII_of_familyHierarchy_and_primeMarkedNonbinary_and_binaryRelatedTripleCoordinate
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
    (nonbinary :
      ∀ (R A : Type x) [Field R] [CommRing A] [HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8),
          NonbinaryPrimeMarkedSolvableIncidenceProvider
            (reductions R A hBase hGroup hE8))
    (binary :
      ∀ (R A : Type x) [Field R] [CommRing A] [HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8),
          BinaryIcosahedralRelatedTripleCoordinateTwoFieldProvider
            (reductions R A hBase hGroup hE8)) :
    Conjecture Base GroupCondition :=
  hierarchy.conjecture_of_e8
    (exactFamilyE8_of_nonbinaryPrimeMarkedSolvableIncidence_and_binaryRelatedTripleCoordinate
      Base GroupCondition family reductions nonbinary binary)

end RiemannResearch.AlgebraicGeometry.SerreII
