/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIINonE8
import RiemannResearch.GaloisCohomology.LocalGaugeTransporter

/-!
# Anchored-gauge provider for the E8 Serre-II branch

This module connects the exact anchored local-gauge transporter criterion for
discrete nonabelian first cohomology to the fpqc neutrality-provider interface
used by the Dynkin-family Serre-II assembly.

The comparison with fpqc cohomology is not postulated globally. Instead, each
presentation contains an explicit reflection implication saying that
coboundary status of its chosen discrete cocycle neutralizes the fpqc class it
represents. Constructing these presentations for algebraic E8 torsors remains
the substantive arithmetic-geometric obligation.
-/

universe u x

namespace RiemannResearch.AlgebraicGeometry.SerreII

open RiemannResearch.GaloisCohomology

/-- Data reducing one pointed-set class to the anchored fixed-gauge criterion
for a discrete nonabelian cocycle.

The internal group, coefficient group, and stabilizer family may depend on the
class. The reflects-neutrality field is the explicit comparison boundary back
to the original pointed set. -/
structure AnchoredGaugePresentation {X : Type x} (point basepoint : X) where
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
  fixedCorrection :
    ∃ c₀ : G, ∀ i,
      NonabelianCocycle.IsFixedBy (stabilizer i)
        (NonabelianCocycle.transition gauge i anchor * c₀)
  reflectsNeutrality : cocycle.IsCoboundary → point = basepoint

namespace AnchoredGaugePresentation

/-- An anchored fixed correction makes the represented pointed-set class
equal to its basepoint. -/
theorem eq_basepoint {X : Type x} {point basepoint : X}
    (P : AnchoredGaugePresentation.{u, x} point basepoint) :
    point = basepoint := by
  let _ : Group P.Γ := P.groupΓ
  let _ : Group P.G := P.groupG
  let _ : MulDistribMulAction P.Γ P.G := P.action
  apply P.reflectsNeutrality
  exact
    (NonabelianCocycle.isCoboundary_iff_exists_anchoredFixedGaugeCorrection
      P.cocycle P.stabilizer P.gauge P.anchor P.generates P.localGauge).2
      P.fixedCorrection

end AnchoredGaugePresentation

/-- Per-class anchored-gauge presentations for every supplied E8 object give
the exact E8 neutrality provider consumed by the full Dynkin-family assembly.

This theorem does not construct the finite-Galois/fpqc comparison or the E8
fixed corrections: both occur visibly in AnchoredGaugePresentation. -/
theorem exactFamilyE8_of_anchoredFixedGaugeCorrections
    (Base : BaseCondition)
    (GroupCondition : GroupCondition)
    (family : DynkinFamilyClassifier)
    (presentations :
      ∀ (R A : CommRingCat.{x}) [HopfAlgebra R A],
        Base R →
        GroupCondition R A →
        family R A = .E8 →
        ∀ ξ : FpqcH1.{x, x} R A,
          Nonempty
            (AnchoredGaugePresentation ξ (FpqcH1.neutral R A))) :
    ExactFamilyNeutralityProvider Base GroupCondition family .E8 := by
  intro R A _ hBase hGroup hE8
  refine ⟨?_⟩
  intro ξ η
  obtain ⟨Pξ⟩ := presentations R A hBase hGroup hE8 ξ
  obtain ⟨Pη⟩ := presentations R A hBase hGroup hE8 η
  exact Pξ.eq_basepoint.trans Pη.eq_basepoint.symm

end RiemannResearch.AlgebraicGeometry.SerreII
