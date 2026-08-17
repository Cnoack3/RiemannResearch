/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIIE8AnchoredGauge
import RiemannResearch.AlgebraicGeometry.SerreIIE8SubsystemFamilyHierarchy
import RiemannResearch.E8.SubgroupSieve
import RiemannResearch.GaloisCohomology.CompatibleLocalGauges

/-!
# Exact completion boundary for the E8 Serre-II program

This module gives a single kernel-checked last-mile reduction for the
toral/subsystem-sieve route in the user-provided Serre-II manuscript.

The finite certificate in E8.SubgroupSieve supplies exactly 31 numerical
perfect-core lift rows. It does not construct algebraic subgroups, field
extensions, Galois classes, or E8-valued gauges. Accordingly, the reduction data
below keeps these mathematical obligations explicit:

* the six proper-subsystem induction maps and Serre-II providers;
* classification of every E8 class as subsystem-induced or as realizing one
  of the 31 certified survivor rows;
* a finite-Galois cocycle presentation of each realized survivor, together
  with its local subsystem gauges and reflection back to Galois neutrality.

The separate commonGauge argument in the terminal theorems is the genuinely
new common-gauge/transporter theorem. It is not deduced here from separate
local gauges, gcd-one orbit degrees, or Conjecture 6.33.

For the mathematical status, proof plan, and references, see
E8/SERRE_II_COMPLETION_PROOF_OBLIGATIONS.md.
-/

universe u x

namespace RiemannResearch.AlgebraicGeometry.SerreII

open RiemannResearch.GaloisCohomology

/-- A discrete nonabelian-cocycle reduction of one pointed-set class after all
separately local subsystem neutralizations have been constructed.

This structure deliberately contains no common gauge and no anchored fixed
correction. That existence statement is exposed as HasCommonGauge. -/
structure AnchoredGaugeReduction {X : Type x} (point basepoint : X) where
  Γ : Type u
  G : Type u
  I : Type u
  [groupΓ : Group Γ]
  [groupG : Group G]
  [action : MulDistribMulAction Γ G]
  cocycle : NonabelianCocycle Γ G
  stabilizer : I → Subgroup Γ
  gauge : I → G
  anchor : I
  generates : (⨆ i, stabilizer i) = ⊤
  localGauge :
    ∀ i, cocycle.IsLocalGauge (stabilizer i) (gauge i)
  /-- The explicit comparison boundary back to the represented Galois class. -/
  reflectsNeutrality : cocycle.IsCoboundary → point = basepoint

namespace AnchoredGaugeReduction

/-- The decisive compatibility assertion: one element is a local gauge on
every subgroup in the generating family. -/
def HasCommonGauge {X : Type x} {point basepoint : X}
    (P : AnchoredGaugeReduction.{u, x} point basepoint) : Prop :=
  let _ : Group P.Γ := P.groupΓ
  let _ : Group P.G := P.groupG
  let _ : MulDistribMulAction P.Γ P.G := P.action
  ∃ b : P.G, ∀ i, P.cocycle.IsLocalGauge (P.stabilizer i) b

/-- The one-anchor fixed-correction form of common-gauge compatibility. -/
def HasAnchoredFixedCorrection {X : Type x} {point basepoint : X}
    (P : AnchoredGaugeReduction.{u, x} point basepoint) : Prop :=
  let _ : Group P.Γ := P.groupΓ
  let _ : Group P.G := P.groupG
  let _ : MulDistribMulAction P.Γ P.G := P.action
  ∃ c₀ : P.G, ∀ i,
    NonabelianCocycle.IsFixedBy (P.stabilizer i)
      (NonabelianCocycle.transition P.gauge i P.anchor * c₀)

/-- Common-gauge compatibility is exactly the anchored fixed-correction
condition. Neither side is asserted to hold automatically. -/
theorem hasCommonGauge_iff_hasAnchoredFixedCorrection
    {X : Type x} {point basepoint : X}
    (P : AnchoredGaugeReduction.{u, x} point basepoint) :
    P.HasCommonGauge ↔ P.HasAnchoredFixedCorrection := by
  let _ : Group P.Γ := P.groupΓ
  let _ : Group P.G := P.groupG
  let _ : MulDistribMulAction P.Γ P.G := P.action
  exact
    (isCoboundary_iff_exists_commonLocalGauge
      P.cocycle P.stabilizer P.generates).symm.trans
      (NonabelianCocycle.isCoboundary_iff_exists_anchoredFixedGaugeCorrection
        P.cocycle P.stabilizer P.gauge P.anchor
        P.generates P.localGauge)

/-- A supplied common gauge neutralizes the represented pointed-set class. -/
theorem eq_basepoint_of_commonGauge
    {X : Type x} {point basepoint : X}
    (P : AnchoredGaugeReduction.{u, x} point basepoint)
    (commonGauge : P.HasCommonGauge) :
    point = basepoint := by
  let _ : Group P.Γ := P.groupΓ
  let _ : Group P.G := P.groupG
  let _ : MulDistribMulAction P.Γ P.G := P.action
  apply P.reflectsNeutrality
  exact
    (isCoboundary_iff_exists_commonLocalGauge
      P.cocycle P.stabilizer P.generates).2 commonGauge

end AnchoredGaugeReduction

/-- The finite type indexing the 31 triality-aligned perfect-core lift rows in
the committed GAP/TomLib certificate. -/
abbrev E8PerfectCoreSurvivorCase : Type :=
  Fin RiemannResearch.E8.omegaEightPlusTwoPerfectCoreLiftData.length

/-- The numerical certificate row indexed by a survivor case. -/
def E8PerfectCoreSurvivorCase.datum
    (survivor : E8PerfectCoreSurvivorCase) :
    RiemannResearch.E8.PerfectCoreLiftDatum :=
  RiemannResearch.E8.omegaEightPlusTwoPerfectCoreLiftData.get survivor

/-- There are exactly 31 certified numerical perfect-core lift rows. -/
theorem E8PerfectCoreSurvivorCase.card :
    Fintype.card E8PerfectCoreSurvivorCase = 31 := by
  simp [E8PerfectCoreSurvivorCase,
    RiemannResearch.E8.omegaEightPlusTwoPerfectCoreLiftData_certificate.1]

/-- All domain-specific reduction data needed before simultaneous E8 gauge
compatibility is invoked.

The fields classify and reduction are not consequences of the numerical
31-row certificate. They include the finite-Galois comparison,
certificate-to-E8 geometry, and separately local subsystem gauges. -/
structure E8SurvivorReductionData {X : Type x} (neutral : X) where
  induction : E8SubsystemInduction.{u, x} neutral
  allSubsystemsSerreII : induction.AllSubsystemsSerreII
  realizes : X → E8PerfectCoreSurvivorCase → Prop
  classify :
    ∀ ξ : X,
      (∃ s, ∃ η : induction.H1 s, induction.induce s η = ξ) ∨
        ∃ survivor, realizes ξ survivor
  reduction :
    ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase),
      realizes ξ survivor → AnchoredGaugeReduction.{u, x} ξ neutral

namespace E8SurvivorReductionData

/-- One class together with a certified survivor row realizing it. Bundling the
class and its realization keeps the dependent reduction proof definitionally
attached to the same class. -/
structure RealizedSurvivor
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral) where
  ξ : X
  survivor : E8PerfectCoreSurvivorCase
  realizes : D.realizes ξ survivor

/-- The anchored reduction determined by a bundled realized survivor. -/
def realizedReduction
    {X : Type x} {neutral : X}
    {D : E8SurvivorReductionData.{u, x} neutral}
    (w : RealizedSurvivor D) :
    AnchoredGaugeReduction.{u, x} w.ξ neutral :=
  D.reduction w.ξ w.survivor w.realizes

/-- Every class is neutral when a common gauge is supplied for every realized
certified survivor. -/
theorem eq_neutral_of_commonGauges
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral)
    (commonGauge :
      ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
        (h : D.realizes ξ survivor),
        (D.reduction ξ survivor h).HasCommonGauge)
    (ξ : X) :
    ξ = neutral := by
  rcases D.classify ξ with hInduced | hSurvivor
  · obtain ⟨s, η, hη⟩ := hInduced
    exact hη ▸ D.induction.induced_eq_neutral D.allSubsystemsSerreII s η
  · obtain ⟨survivor, hrealizes⟩ := hSurvivor
    exact
      (D.reduction ξ survivor hrealizes).eq_basepoint_of_commonGauge
        (commonGauge ξ survivor hrealizes)

end E8SurvivorReductionData

/-- Completion of the exact E8 Dynkin-family branch from the six-subsystem
reduction, the certified 31-survivor reduction, and the separately supplied
common-gauge theorem. -/
theorem exactFamilyE8_of_certifiedSurvivorCommonGauges
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (reductions :
      ∀ (R A : Type x) [field : Field R] [ring : CommRing A] [hopf : HopfAlgebra R A],
        Base R →
        GroupCondition R A →
        family R A = .E8 →
          E8SurvivorReductionData.{u, x} (GaloisH1.neutral R A))
    (commonGauge :
      ∀ (R A : Type x) [field : Field R] [ring : CommRing A] [hopf : HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8)
        (w : E8SurvivorReductionData.RealizedSurvivor
          (@reductions R A field ring hopf hBase hGroup hE8)),
        (E8SurvivorReductionData.realizedReduction w).HasCommonGauge) :
    ExactFamilyNeutralityProvider Base GroupCondition family .E8 := by
  intro R A field ring hopf hBase hGroup hE8
  let D := @reductions R A field ring hopf hBase hGroup hE8
  have hcommon :
      ∀ (ξ : GaloisH1 R A)
        (survivor : E8PerfectCoreSurvivorCase)
        (hrealizes : D.realizes ξ survivor),
        (D.reduction ξ survivor hrealizes).HasCommonGauge := by
    intro ξ survivor hrealizes
    let w : E8SurvivorReductionData.RealizedSurvivor D :=
      ⟨ξ, survivor, hrealizes⟩
    simpa [D, w, E8SurvivorReductionData.realizedReduction] using
      @commonGauge R A field ring hopf hBase hGroup hE8 w
  refine ⟨?_⟩
  intro ξ η
  exact
    (D.eq_neutral_of_commonGauges hcommon ξ).trans
      (D.eq_neutral_of_commonGauges hcommon η).symm

/-- Single terminal reduction: non-E8 Serre II plus the explicit E8
subsystem/survivor reductions and common-gauge theorem imply the supplied
full H1 target.

This is a conditional research reduction. The reductions argument contains
the finite-Galois realization boundary, while commonGauge is precisely
the open simultaneous E8 compatibility theorem. -/
theorem serreII_of_nonE8_and_certifiedSurvivorCommonGauges
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (nonE8 :
      Conjecture Base (NonE8GroupCondition GroupCondition family))
    (reductions :
      ∀ (R A : Type x) [field : Field R] [ring : CommRing A] [hopf : HopfAlgebra R A],
        Base R →
        GroupCondition R A →
        family R A = .E8 →
          E8SurvivorReductionData.{u, x} (GaloisH1.neutral R A))
    (commonGauge :
      ∀ (R A : Type x) [field : Field R] [ring : CommRing A] [hopf : HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8)
        (w : E8SurvivorReductionData.RealizedSurvivor
          (@reductions R A field ring hopf hBase hGroup hE8)),
        (E8SurvivorReductionData.realizedReduction w).HasCommonGauge) :
    Conjecture Base GroupCondition :=
  conjecture_of_nonE8_and_e8 Base GroupCondition family nonE8
    (exactFamilyE8_of_certifiedSurvivorCommonGauges
      Base GroupCondition family reductions commonGauge)

/-- Shared-family-hierarchy form of the terminal reduction. All proper
Dynkin-family developments enter through one reusable hierarchy, while the
certified survivor reduction and common-gauge theorem supply the `E8`
branch. -/
theorem serreII_of_familyHierarchy_and_certifiedSurvivorCommonGauges
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (hierarchy :
      NonE8FamilyNeutralityHierarchy Base GroupCondition family)
    (reductions :
      ∀ (R A : Type x) [field : Field R] [ring : CommRing A] [hopf : HopfAlgebra R A],
        Base R →
        GroupCondition R A →
        family R A = .E8 →
          E8SurvivorReductionData.{u, x} (GaloisH1.neutral R A))
    (commonGauge :
      ∀ (R A : Type x) [field : Field R] [ring : CommRing A] [hopf : HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8)
        (w : E8SurvivorReductionData.RealizedSurvivor
          (@reductions R A field ring hopf hBase hGroup hE8)),
        (E8SurvivorReductionData.realizedReduction w).HasCommonGauge) :
    Conjecture Base GroupCondition :=
  hierarchy.conjecture_of_e8
    (exactFamilyE8_of_certifiedSurvivorCommonGauges
      Base GroupCondition family reductions commonGauge)

/-- Fully exposed family-provider form of the terminal reduction. Exact
providers for A, B, C, D, E6, E7, F4, and G2, together with the E8 reductions
and common-gauge theorem, imply the supplied full H1 target. -/
theorem serreII_of_exactFamilies_and_certifiedSurvivorCommonGauges
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (a : ExactFamilyNeutralityProvider Base GroupCondition family .A)
    (b : ExactFamilyNeutralityProvider Base GroupCondition family .B)
    (c : ExactFamilyNeutralityProvider Base GroupCondition family .C)
    (d : ExactFamilyNeutralityProvider Base GroupCondition family .D)
    (e6 : ExactFamilyNeutralityProvider Base GroupCondition family .E6)
    (e7 : ExactFamilyNeutralityProvider Base GroupCondition family .E7)
    (f4 : ExactFamilyNeutralityProvider Base GroupCondition family .F4)
    (g2 : ExactFamilyNeutralityProvider Base GroupCondition family .G2)
    (reductions :
      ∀ (R A : Type x) [field : Field R] [ring : CommRing A] [hopf : HopfAlgebra R A],
        Base R →
        GroupCondition R A →
        family R A = .E8 →
          E8SurvivorReductionData.{u, x} (GaloisH1.neutral R A))
    (commonGauge :
      ∀ (R A : Type x) [field : Field R] [ring : CommRing A] [hopf : HopfAlgebra R A]
        (hBase : Base R) (hGroup : GroupCondition R A)
        (hE8 : family R A = .E8)
        (w : E8SurvivorReductionData.RealizedSurvivor
          (@reductions R A field ring hopf hBase hGroup hE8)),
        (E8SurvivorReductionData.realizedReduction w).HasCommonGauge) :
    Conjecture Base GroupCondition :=
  serreII_of_familyHierarchy_and_certifiedSurvivorCommonGauges
    Base GroupCondition family
    (NonE8FamilyNeutralityHierarchy.of_exact_providers
      Base GroupCondition family a b c d e6 e7 f4 g2)
    reductions commonGauge

end RiemannResearch.AlgebraicGeometry.SerreII
