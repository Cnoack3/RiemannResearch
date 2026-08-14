/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.E8.PrimeMarkedPacket
import RiemannResearch.GaloisCohomology.CoprimeTorusFiltration

/-!
# Prime-marked additive detection and solvable incidence

This module combines the certified E8 packet degrees 135, 11200, and 12096
with arbitrary finite-index restriction/corestriction in additive H¹. It
then supplies packet-specialized conditional endpoints for the solvable-band
argument: a single chosen gauge into `B`, one residual additive class, its
vanishing on the three packet stabilizers, a correction into `U`, and
terminal `U`-vanishing produce global neutrality and the anchored correction.

No declaration constructs the chosen common band, a Borel, a Deodhar chart,
or a field-valued transporter for any of the 31 survivors. Those are the
open strong-E8 geometric inputs.

Source: user-provided strong-E8 solvable-incidence argument (14 August 2026);
the source supports the statements and proof strategy.
-/

open CategoryTheory

universe u v w

namespace RiemannResearch.E8

open RiemannResearch.GroupCohomology

/-- Restrictions to finite-index subgroups of the three prime-marked E8
degrees jointly detect zero in additive H¹. -/
theorem h1_eq_zero_of_primeMarkedPacket_restrictions
    {k Γ : Type u} [CommRing k] [Group Γ]
    (A : Rep k Γ) (H2 H3 H5 : Subgroup Γ)
    [H2.FiniteIndex] [H3.FiniteIndex] [H5.FiniteIndex]
    (hcard2 : Nat.card (Γ ⧸ H2) = 135)
    (hcard3 : Nat.card (Γ ⧸ H3) = 11_200)
    (hcard5 : Nat.card (Γ ⧸ H5) = 12_096)
    {x : groupCohomology.H1 A}
    (hres2 : h1RestrictionViaCocycles A H2 x = 0)
    (hres3 : h1RestrictionViaCocycles A H3 x = 0)
    (hres5 : h1RestrictionViaCocycles A H5 x = 0) :
    x = 0 := by
  apply eq_zero_of_primeMarkedPacket_annihilators
  · have hcomp :=
      h1RestrictionViaCocycles_comp_h1CorestrictionFiniteIndex A H2
    have happ := congrArg
      (fun f : groupCohomology.H1 A ⟶ groupCohomology.H1 A => f x) hcomp
    simpa [hres2, hcard2] using happ.symm
  · have hcomp :=
      h1RestrictionViaCocycles_comp_h1CorestrictionFiniteIndex A H3
    have happ := congrArg
      (fun f : groupCohomology.H1 A ⟶ groupCohomology.H1 A => f x) hcomp
    simpa [hres3, hcard3] using happ.symm
  · have hcomp :=
      h1RestrictionViaCocycles_comp_h1CorestrictionFiniteIndex A H5
    have happ := congrArg
      (fun f : groupCohomology.H1 A ⟶ groupCohomology.H1 A => f x) hcomp
    simpa [hres5, hcard5] using happ.symm

end RiemannResearch.E8

namespace RiemannResearch.GaloisCohomology

open RiemannResearch.GroupCohomology

/-- The exact 135/11200/12096 solvable-incidence criterion for one chosen
band-valued gauge. -/
theorem NonabelianCocycle.isCoboundary_of_primeMarked_solvableIncidence
    {k Γ : Type u} {G : Type v}
    [CommRing k] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G) (B U : Subgroup G)
    (T : Rep k Γ) (H2 H3 H5 : Subgroup Γ)
    [H2.FiniteIndex] [H3.FiniteIndex] [H5.FiniteIndex]
    (hcard2 : Nat.card (Γ ⧸ H2) = 135)
    (hcard3 : Nat.card (Γ ⧸ H3) = 11_200)
    (hcard5 : Nat.card (Γ ⧸ H5) = 12_096)
    (r : G) (_hz : (a.gauge r).ValuesIn B)
    (x : groupCohomology.H1 T)
    (hres2 : h1RestrictionViaCocycles T H2 x = 0)
    (hres3 : h1RestrictionViaCocycles T H3 x = 0)
    (hres5 : h1RestrictionViaCocycles T H5 x = 0)
    (gaugeIntoU_of_x_zero :
      x = 0 →
        ∃ q : B, ((a.gauge r).gauge (q : G)).ValuesIn U)
    (hU :
      ∀ z : NonabelianCocycle Γ G, z.ValuesIn U → z.IsCoboundary) :
    a.IsCoboundary := by
  have hx : x = 0 :=
    RiemannResearch.E8.h1_eq_zero_of_primeMarkedPacket_restrictions
      T H2 H3 H5 hcard2 hcard3 hcard5 hres2 hres3 hres5
  obtain ⟨q, hq⟩ := gaugeIntoU_of_x_zero hx
  have hcorrected :
      ((a.gauge r).gauge (q : G)).IsCoboundary :=
    hU _ hq
  have hgauged : (a.gauge r).IsCoboundary :=
    ((a.gauge r).isCoboundary_gauge_iff (q : G)).1 hcorrected
  exact (a.isCoboundary_gauge_iff r).1 hgauged

/-- The packet-specialized solvable-incidence argument produces the anchored
fixed correction of Research Target 7.1 for the entire generating family. -/
theorem NonabelianCocycle.exists_anchoredFixedGaugeCorrection_of_primeMarked_solvableIncidence
    {k Γ : Type u} {G : Type v}
    [CommRing k] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G) (B U : Subgroup G)
    {I : Type w} (T : Rep k Γ) (H : I → Subgroup Γ)
    (i2 i3 i5 anchor : I)
    [(H i2).FiniteIndex] [(H i3).FiniteIndex] [(H i5).FiniteIndex]
    (hcard2 : Nat.card (Γ ⧸ H i2) = 135)
    (hcard3 : Nat.card (Γ ⧸ H i3) = 11_200)
    (hcard5 : Nat.card (Γ ⧸ H i5) = 12_096)
    (localGauge : I → G)
    (hgen : (⨆ i, H i) = ⊤)
    (hlocal : ∀ i, a.IsLocalGauge (H i) (localGauge i))
    (r : G) (hz : (a.gauge r).ValuesIn B)
    (x : groupCohomology.H1 T)
    (hres2 : h1RestrictionViaCocycles T (H i2) x = 0)
    (hres3 : h1RestrictionViaCocycles T (H i3) x = 0)
    (hres5 : h1RestrictionViaCocycles T (H i5) x = 0)
    (gaugeIntoU_of_x_zero :
      x = 0 →
        ∃ q : B, ((a.gauge r).gauge (q : G)).ValuesIn U)
    (hU :
      ∀ z : NonabelianCocycle Γ G, z.ValuesIn U → z.IsCoboundary) :
    ∃ c₀ : G, ∀ i,
      NonabelianCocycle.IsFixedBy (H i)
        (NonabelianCocycle.transition localGauge i anchor * c₀) := by
  apply
    (NonabelianCocycle.isCoboundary_iff_exists_anchoredFixedGaugeCorrection
      a H localGauge anchor hgen hlocal).1
  exact a.isCoboundary_of_primeMarked_solvableIncidence
    B U T (H i2) (H i3) (H i5)
      hcard2 hcard3 hcard5 r hz x hres2 hres3 hres5
        gaugeIntoU_of_x_zero hU

end RiemannResearch.GaloisCohomology
