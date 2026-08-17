/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIIE8TrialityReduction
import RiemannResearch.E8.BinaryIcosahedralSubgroups
import RiemannResearch.Logic.PointedKernel

/-!
# Binary-icosahedral two-field reduction for E8

Let a common finite Galois splitting field have group
SL(2, F_5) = 2.A_5. The certified subgroup diamond supplies

* the binary-tetrahedral subgroup H, of order 24 and index 5;
* the binary-dihedral subgroup K, of order 20 and index 6;
* H ⊔ K = ⊤.

The index-five and index-six fixed fields are not generally Galois over the
base, so Gille's cyclic theorem cannot be applied directly to those two
extensions. Instead one applies it successively up the Galois extensions with
groups H and K, using cyclic composition factors of orders 2, 3, and 5.
The two composite trivial-kernel statements below record the outcome: the
global cocycle is locally a coboundary on both H and K.

Separate local gauges need not agree. The final input is therefore precisely
the oriented transition-factorization theorem isolated by
BinaryIcosahedralSubgroups. Since H and K generate 2.A_5, that factorization
turns the two local gauges into one global coboundary.

This module is an honest conditional reduction. It does not yet construct the
finite Galois realization of an E8 torsor, the two cyclic composition towers,
or the E8-specific oriented transporter and its factorization. In particular,
coprimality of the two field degrees 5 and 6 alone is not used as a
nonabelian restriction-corestriction argument.

External inputs motivating the two composite kernel fields:

* Philippe Gille, “Cohomologie galoisienne des groupes quasi-déployés sur des
  corps de dimension cohomologique ≤ 2,” *Compositio Mathematica* 125 (2001),
  Theorem 11, <https://doi.org/10.1023/A:1002473132282>.
* Burt Totaro, “Splitting fields for E8-torsors,” *Duke Mathematical Journal*
  121 (2004), 425–455, <https://doi.org/10.1215/S0012-7094-04-12132-5>.
-/

universe u x

namespace RiemannResearch.AlgebraicGeometry.SerreII

open RiemannResearch.Logic
open RiemannResearch.GaloisCohomology
open RiemannResearch.E8.BinaryIcosahedralSubgroups

/-- The exact binary-icosahedral two-field data needed to neutralize one
realized E8 class.

The two HasTrivialKernel fields are the composites obtained by iterating
Gille along cyclic composition towers from the index-five and index-six fixed
fields to the common splitting field. The transporter fields expose the
remaining E8-specific compatibility problem between the two resulting local
gauges. -/
structure BinaryIcosahedralGilleTwoFieldPresentation
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
  factorization :
    ∀ y : G,
      IsAdmissibleTwoGaugeTransition
        binaryTetrahedralSubgroup binaryDihedralSubgroup y →
      y ∈ orientedSubgroupTransporter S6 S5 theta →
      ∃ a b : G,
        NonabelianCocycle.IsFixedBy binaryTetrahedralSubgroup a ∧
        NonabelianCocycle.IsFixedBy binaryDihedralSubgroup b ∧
        y = a * b
  reflectsNeutrality : cocycle.IsCoboundary → point = neutral

namespace BinaryIcosahedralGilleTwoFieldPresentation

/-- The binary-icosahedral two-field reduction.

Iterated Gille kernels make the restrictions to the binary-tetrahedral and
binary-dihedral subgroups coboundaries. The oriented
transition-factorization theorem then glues their gauges because those two
subgroups generate SL(2, F_5). -/
theorem eq_basepoint
    {X : Type x} {point neutral : X}
    (P : BinaryIcosahedralGilleTwoFieldPresentation.{u, x} point neutral) :
    point = neutral := by
  let _ : Group P.G := P.groupG
  let _ : MulDistribMulAction SL2F5 P.G := P.action
  let xH : NonabelianH1 binaryTetrahedralSubgroup P.G :=
    NonabelianH1.classOf
      (P.cocycle.restrict binaryTetrahedralSubgroup)
  have hxHtop :
      NonabelianH1.restrict
          (⊥ : Subgroup binaryTetrahedralSubgroup) xH =
        (NonabelianH1.neutral :
          NonabelianH1 (⊥ : Subgroup binaryTetrahedralSubgroup) P.G) :=
    NonabelianH1.restrict_bot_eq_neutral xH
  have hxH :
      xH =
        (NonabelianH1.neutral :
          NonabelianH1 binaryTetrahedralSubgroup P.G) :=
    (P.tetrahedralGilleKernel xH).1 hxHtop
  have hHcob :
      (P.cocycle.restrict binaryTetrahedralSubgroup).IsCoboundary :=
    (NonabelianH1.classOf_eq_neutral_iff_isCoboundary _).1 hxH
  let xK : NonabelianH1 binaryDihedralSubgroup P.G :=
    NonabelianH1.classOf
      (P.cocycle.restrict binaryDihedralSubgroup)
  have hxKtop :
      NonabelianH1.restrict
          (⊥ : Subgroup binaryDihedralSubgroup) xK =
        (NonabelianH1.neutral :
          NonabelianH1 (⊥ : Subgroup binaryDihedralSubgroup) P.G) :=
    NonabelianH1.restrict_bot_eq_neutral xK
  have hxK :
      xK =
        (NonabelianH1.neutral :
          NonabelianH1 binaryDihedralSubgroup P.G) :=
    (P.dihedralGilleKernel xK).1 hxKtop
  have hKcob :
      (P.cocycle.restrict binaryDihedralSubgroup).IsCoboundary :=
    (NonabelianH1.classOf_eq_neutral_iff_isCoboundary _).1 hxK
  obtain ⟨gH, hgH⟩ := hHcob
  obtain ⟨gK, hgK⟩ := hKcob
  have hH : ∀ σ : binaryTetrahedralSubgroup,
      P.cocycle σ.1 = gH⁻¹ * σ.1 • gH := by
    intro σ
    have h := congrArg
      (fun z : NonabelianCocycle binaryTetrahedralSubgroup P.G => z σ) hgH
    simpa [NonabelianCocycle.restrict, NonabelianCocycle.gauge,
      NonabelianCocycle.trivial, Subgroup.smul_def] using h
  have hK : ∀ σ : binaryDihedralSubgroup,
      P.cocycle σ.1 = gK⁻¹ * σ.1 • gK := by
    intro σ
    have h := congrArg
      (fun z : NonabelianCocycle binaryDihedralSubgroup P.G => z σ) hgK
    simpa [NonabelianCocycle.restrict, NonabelianCocycle.gauge,
      NonabelianCocycle.trivial, Subgroup.smul_def] using h
  apply P.reflectsNeutrality
  exact
    isCoboundary_of_binaryIcosahedral_admissible_orientedTransition_factorization
      P.cocycle gH gK hH hK P.S6 P.S5 P.theta
      (P.orientedTransition gH gK hH hK) P.factorization

end BinaryIcosahedralGilleTwoFieldPresentation

/-- A two-field presentation for every realized binary-icosahedral survivor
row. The finite-Galois comparison and the E8 transporter geometry are
deliberately kept inside the supplied presentation. -/
structure BinaryIcosahedralGilleTwoFieldProvider
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral) where
  presentation :
    ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
      (_h : D.realizes ξ survivor),
      survivor.IsBinaryIcosahedral →
        BinaryIcosahedralGilleTwoFieldPresentation.{u, x} ξ neutral

namespace E8SurvivorReductionData

/-- The sharpened 4 + 27 E8 assembly.

The twenty-seven nonbinary survivor rows retain their common-gauge
obligations. Each of the four binary-icosahedral rows is instead neutralized
by its binary-tetrahedral/binary-dihedral two-field presentation. -/
theorem
    eq_neutral_of_nonbinaryCommonGauges_and_binaryIcosahedralGilleTwoField
    {X : Type x} {neutral : X}
    (D : E8SurvivorReductionData.{u, x} neutral)
    (nonbinaryCommonGauge :
      ∀ (ξ : X) (survivor : E8PerfectCoreSurvivorCase)
        (_h : D.realizes ξ survivor),
        ¬ survivor.IsBinaryIcosahedral →
          (D.reduction ξ survivor _h).HasCommonGauge)
    (binary : BinaryIcosahedralGilleTwoFieldProvider D)
    (ξ : X) :
    ξ = neutral := by
  rcases D.classify ξ with hInduced | hSurvivor
  · obtain ⟨s, η, hη⟩ := hInduced
    exact
      hη ▸ D.induction.induced_eq_neutral
        D.allSubsystemsSerreII s η
  · obtain ⟨survivor, hrealizes⟩ := hSurvivor
    by_cases hs : survivor.IsBinaryIcosahedral
    · exact
        (binary.presentation ξ survivor hrealizes hs).eq_basepoint
    · exact
        (D.reduction ξ survivor hrealizes).eq_basepoint_of_commonGauge
          (nonbinaryCommonGauge ξ survivor hrealizes hs)

end E8SurvivorReductionData

/-- Exact E8 family provider from twenty-seven nonbinary common gauges and
the binary-icosahedral two-field reduction on the remaining four rows. -/
theorem
    exactFamilyE8_of_nonbinaryCommonGauges_and_binaryIcosahedralGilleTwoField
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
          BinaryIcosahedralGilleTwoFieldProvider
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
  let B : BinaryIcosahedralGilleTwoFieldProvider D := by
    simpa [D] using binary R A hBase hGroup hE8
  constructor
  intro ξ η
  exact
    (D.eq_neutral_of_nonbinaryCommonGauges_and_binaryIcosahedralGilleTwoField
      hnonbinary B ξ).trans
    (D.eq_neutral_of_nonbinaryCommonGauges_and_binaryIcosahedralGilleTwoField
      hnonbinary B η).symm

/-- Terminal family-hierarchy reduction using the binary-icosahedral
two-field argument on the four exceptional E8 rows. -/
theorem serreII_of_familyHierarchy_and_binaryIcosahedralGilleTwoField
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
          BinaryIcosahedralGilleTwoFieldProvider
            (reductions R A hBase hGroup hE8)) :
    Conjecture Base GroupCondition :=
  hierarchy.conjecture_of_e8
    (exactFamilyE8_of_nonbinaryCommonGauges_and_binaryIcosahedralGilleTwoField
      Base GroupCondition family reductions nonbinaryCommonGauge binary)

end RiemannResearch.AlgebraicGeometry.SerreII
