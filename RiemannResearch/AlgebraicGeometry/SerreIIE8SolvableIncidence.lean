/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.SerreIIE8Completion
import RiemannResearch.GaloisCohomology.CoprimeTorusFiltration

/-!
# Solvable-incidence completion boundary for E8

This module packages the rigorous cohomological part of the proposed strong
E8 argument. A certificate records one chosen simultaneous gauge into a
common coefficient subgroup `B`, one residual additive H¹ class detected by
a gcd-one family of stabilizers, a correction into `U`, and terminal
`U`-vanishing. Such a certificate yields a common gauge, the anchored fixed
correction, and neutrality of the represented fpqc class.

The structure does not manufacture its hard geometric fields. In the E8
application, a simultaneous typed transporter/Deodhar calculation must still
construct `bandGauge` and `bandValued`, prove that all packet-local points
belong to the same descended solvable torsor component, identify the residual
torus class, and prove the unipotent height-filtration vanishing. Pairwise
Weyl-cell data alone does not supply these fields.

Source: user-provided strong-E8 solvable-incidence argument (14 August 2026);
the source supports the conditional reduction and terminology.
-/

universe u v w x

namespace RiemannResearch.AlgebraicGeometry.SerreII

open RiemannResearch.GaloisCohomology
open RiemannResearch.GroupCohomology

/-- The algebraic output required from one global solvable-incidence
component. It deliberately separates the common-band gauge, residual
additive obstruction, correction to `U`, and terminal `U`-vanishing. -/
structure ChosenGaugeSolvableFiltrationCertificate
    {k Γ : Type u} {G : Type v} {I : Type w}
    [CommRing k] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G) (S : I → Subgroup Γ) where
  B : Subgroup G
  U : Subgroup G
  finiteIndex : ∀ i, (S i).FiniteIndex
  T : Rep k Γ
  support : Finset I
  gcd_one :
    support.gcd (fun i => (Nat.card (Γ ⧸ S i) : ℤ)) = 1
  bandGauge : G
  bandValued : (a.gauge bandGauge).ValuesIn B
  obstruction : groupCohomology.H1 T
  obstruction_local :
    ∀ i, i ∈ support →
      h1RestrictionViaCocycles T (S i) obstruction = 0
  correct_to_unipotent :
    obstruction = 0 →
      ∃ q : B, ((a.gauge bandGauge).gauge (q : G)).ValuesIn U
  unipotent_h1 :
    ∀ z : NonabelianCocycle Γ G, z.ValuesIn U → z.IsCoboundary

namespace ChosenGaugeSolvableFiltrationCertificate

theorem isCoboundary
    {k Γ : Type u} {G : Type v} {I : Type w}
    [CommRing k] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    {a : NonabelianCocycle Γ G} {S : I → Subgroup Γ}
    (C : ChosenGaugeSolvableFiltrationCertificate (k := k) a S) :
    a.IsCoboundary := by
  let _ : ∀ i, (S i).FiniteIndex := C.finiteIndex
  exact
    a.isCoboundary_of_chosen_gauge_subgroup_filtration_gcd_one_h1
      C.B C.U C.T S C.support C.gcd_one
      C.bandGauge C.bandValued
      C.obstruction C.obstruction_local
      C.correct_to_unipotent C.unipotent_h1

theorem exists_commonLocalGauge
    {k Γ : Type u} {G : Type v} {I : Type w}
    [CommRing k] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    {a : NonabelianCocycle Γ G} {S : I → Subgroup Γ}
    (C : ChosenGaugeSolvableFiltrationCertificate (k := k) a S)
    (hgen : (⨆ i, S i) = ⊤) :
    ∃ b : G, ∀ i, a.IsLocalGauge (S i) b := by
  let _ : ∀ i, (S i).FiniteIndex := C.finiteIndex
  exact
    a.exists_commonLocalGauge_of_chosen_gauge_subgroup_filtration_gcd_one_h1
      C.B C.U C.T S C.support C.gcd_one hgen
      C.bandGauge C.bandValued
      C.obstruction C.obstruction_local
      C.correct_to_unipotent C.unipotent_h1

end ChosenGaugeSolvableFiltrationCertificate

namespace AnchoredGaugeReduction

/-- A strong-E8 solvable-incidence certificate attached to one survivor
reduction. The coefficient ring is stored because the residual obstruction
is an additive representation-valued H¹ class. -/
structure SolvableIncidenceCertificate
    {X : Type x} {point basepoint : X}
    (P : AnchoredGaugeReduction.{u, x} point basepoint) where
  k : Type u
  commRingK : CommRing k
  core :
    let _ : CommRing k := commRingK
    let _ : Group P.Γ := P.groupΓ
    let _ : Group P.G := P.groupG
    let _ : MulDistribMulAction P.Γ P.G := P.action
    ChosenGaugeSolvableFiltrationCertificate (k := k)
      P.cocycle P.stabilizer

theorem hasCommonGauge_of_solvableIncidenceCertificate
    {X : Type x} {point basepoint : X}
    (P : AnchoredGaugeReduction.{u, x} point basepoint)
    (C : P.SolvableIncidenceCertificate) :
    P.HasCommonGauge := by
  let _ : CommRing C.k := C.commRingK
  let _ : Group P.Γ := P.groupΓ
  let _ : Group P.G := P.groupG
  let _ : MulDistribMulAction P.Γ P.G := P.action
  exact C.core.exists_commonLocalGauge P.generates

theorem hasAnchoredFixedCorrection_of_solvableIncidenceCertificate
    {X : Type x} {point basepoint : X}
    (P : AnchoredGaugeReduction.{u, x} point basepoint)
    (C : P.SolvableIncidenceCertificate) :
    P.HasAnchoredFixedCorrection :=
  (P.hasCommonGauge_iff_hasAnchoredFixedCorrection).1
    (P.hasCommonGauge_of_solvableIncidenceCertificate C)

theorem eq_basepoint_of_solvableIncidenceCertificate
    {X : Type x} {point basepoint : X}
    (P : AnchoredGaugeReduction.{u, x} point basepoint)
    (C : P.SolvableIncidenceCertificate) :
    point = basepoint :=
  P.eq_basepoint_of_commonGauge
    (P.hasCommonGauge_of_solvableIncidenceCertificate C)

end AnchoredGaugeReduction

namespace E8SurvivorReductionData

theorem eq_neutral_of_solvableIncidenceCertificates
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral)
    (certificates :
      ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
        (h : D.realizes ξ survivor),
        (D.reduction ξ survivor h).SolvableIncidenceCertificate)
    (ξ : X) :
    ξ = neutral :=
  D.eq_neutral_of_commonGauges
    (fun ξ survivor h =>
      (D.reduction ξ survivor h).hasCommonGauge_of_solvableIncidenceCertificate
        (certificates ξ survivor h))
    ξ

end E8SurvivorReductionData

/-- Certificates for all realized survivor cases supply the exact E8 family
provider. This is a conditional research reduction: construction of the
certificates is the remaining strong-E8 geometric theorem. -/
theorem exactFamilyE8_of_certifiedSurvivorSolvableIncidence
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (reductions :
      ∀ (R A : CommRingCat.{x}) [HopfAlgebra R A],
        Base R →
        GroupCondition R A →
        family R A = DynkinFamily.E8 →
        E8SurvivorReductionData.{u, x + 1}
          (FpqcH1.neutral R A))
    (certificates :
      ∀ (R A : CommRingCat.{x}) [HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = DynkinFamily.E8)
        (ξ : FpqcH1 R A)
        (survivor : E8PerfectCoreSurvivorCase)
        (hrealizes :
          (reductions R A hBase hGroup hE8).realizes ξ survivor),
        ((reductions R A hBase hGroup hE8).reduction
          ξ survivor hrealizes).SolvableIncidenceCertificate) :
    ExactFamilyNeutralityProvider
      Base GroupCondition family DynkinFamily.E8 :=
  exactFamilyE8_of_certifiedSurvivorCommonGauges
    Base GroupCondition family reductions
    (fun R A _ hBase hGroup hE8 ξ survivor hrealizes =>
      let P :=
        (reductions R A hBase hGroup hE8).reduction
          ξ survivor hrealizes
      P.hasCommonGauge_of_solvableIncidenceCertificate
        (certificates R A hBase hGroup hE8
          ξ survivor hrealizes))

end RiemannResearch.AlgebraicGeometry.SerreII
