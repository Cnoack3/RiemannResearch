/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.CompatibleLocalGauges
import RiemannResearch.GaloisCohomology.SubgroupFiltration
import RiemannResearch.GroupCohomology.CoprimeRestrictionDetection

/-!
# Coprime detection in a subgroup filtration

This module supplies the abelian middle step in a Borel--torus--unipotent
reduction. Once a simultaneous field-valued gauge puts a nonabelian cocycle
inside one Galois-stable Borel, the residual torus obstruction is an additive
H¹ class. If its restrictions vanish on a finite family of subgroup
stabilizers whose indices have gcd one, arbitrary corestriction and Bézout
descent kill the obstruction globally. A subsequent gauge into the
unipotent radical and unipotent H¹ vanishing then produce a common gauge.

Source: user-provided Research Target 7.1 analysis (14 August 2026); the source
supports the Borel/torus/unipotent interpretation and the application.
-/

universe u v w

namespace RiemannResearch.GaloisCohomology

open RiemannResearch.GroupCohomology

/-- A residual abelian H¹ obstruction detected by a gcd-one family of
subgroups supplies the middle step in a subgroup filtration. -/
theorem NonabelianCocycle.isCoboundary_of_subgroup_filtration_gcd_one_h1
    {k Γ : Type u} {G : Type v}
    [CommRing k] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G) (B U : Subgroup G)
    {ι : Type w} (T : Rep k Γ) (S : ι → Subgroup Γ)
    [∀ i, (S i).FiniteIndex]
    (s : Finset ι)
    (hgcd : s.gcd (fun i => (Nat.card (Γ ⧸ S i) : ℤ)) = 1)
    (hB : a.CanGaugeInto B)
    (obstruction :
      ∀ z : NonabelianCocycle Γ G, z.ValuesIn B →
        groupCohomology.H1 T)
    (obstruction_restricts_to_zero :
      ∀ (z : NonabelianCocycle Γ G) (hz : z.ValuesIn B)
        (i : ι), i ∈ s →
          h1RestrictionViaCocycles T (S i) (obstruction z hz) = 0)
    (gaugeIntoU_of_obstruction_zero :
      ∀ (z : NonabelianCocycle Γ G) (hz : z.ValuesIn B),
        obstruction z hz = 0 →
          ∃ q : B, (z.gauge (q : G)).ValuesIn U)
    (hU :
      ∀ z : NonabelianCocycle Γ G, z.ValuesIn U → z.IsCoboundary) :
    a.IsCoboundary := by
  apply a.isCoboundary_of_subgroup_filtration B U hB
  · intro z hz
    apply gaugeIntoU_of_obstruction_zero z hz
    exact h1_eq_zero_of_gcd_one_restrictions T S s hgcd
      (obstruction_restricts_to_zero z hz)
  · exact hU

/-- The same coprime-index filtration directly supplies the common gauge
required by the local-gauge transporter criterion. -/
theorem NonabelianCocycle.exists_commonLocalGauge_of_subgroup_filtration_gcd_one_h1
    {k Γ : Type u} {G : Type v}
    [CommRing k] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G) (B U : Subgroup G)
    {ι : Type w} (T : Rep k Γ) (S : ι → Subgroup Γ)
    [∀ i, (S i).FiniteIndex]
    (s : Finset ι)
    (hgcd : s.gcd (fun i => (Nat.card (Γ ⧸ S i) : ℤ)) = 1)
    (hgen : (⨆ i, S i) = ⊤)
    (hB : a.CanGaugeInto B)
    (obstruction :
      ∀ z : NonabelianCocycle Γ G, z.ValuesIn B →
        groupCohomology.H1 T)
    (obstruction_restricts_to_zero :
      ∀ (z : NonabelianCocycle Γ G) (hz : z.ValuesIn B)
        (i : ι), i ∈ s →
          h1RestrictionViaCocycles T (S i) (obstruction z hz) = 0)
    (gaugeIntoU_of_obstruction_zero :
      ∀ (z : NonabelianCocycle Γ G) (hz : z.ValuesIn B),
        obstruction z hz = 0 →
          ∃ q : B, (z.gauge (q : G)).ValuesIn U)
    (hU :
      ∀ z : NonabelianCocycle Γ G, z.ValuesIn U → z.IsCoboundary) :
    ∃ b : G, ∀ i, a.IsLocalGauge (S i) b := by
  apply (isCoboundary_iff_exists_commonLocalGauge a S hgen).1
  exact a.isCoboundary_of_subgroup_filtration_gcd_one_h1
    B U T S s hgcd hB obstruction obstruction_restricts_to_zero
      gaugeIntoU_of_obstruction_zero hU

/-- A chosen common-`B` gauge needs only its own residual H¹ obstruction.

Unlike `isCoboundary_of_subgroup_filtration_gcd_one_h1`, this theorem does
not ask for an obstruction construction and a correction theorem for every
`B`-valued cocycle. It starts with the one gauge `r` supplied by the
simultaneous common-Borel reduction and the one additive class `x` attached
to that reduction. Coprime-index detection kills `x`; the supplied lift of
that single vanishing statement then gauges the cocycle into `U`. -/
theorem NonabelianCocycle.isCoboundary_of_chosen_gauge_subgroup_filtration_gcd_one_h1
    {k Γ : Type u} {G : Type v}
    [CommRing k] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G) (B U : Subgroup G)
    {ι : Type w} (T : Rep k Γ) (S : ι → Subgroup Γ)
    [∀ i, (S i).FiniteIndex]
    (s : Finset ι)
    (hgcd : s.gcd (fun i => (Nat.card (Γ ⧸ S i) : ℤ)) = 1)
    (r : G) (_hz : (a.gauge r).ValuesIn B)
    (x : groupCohomology.H1 T)
    (x_restricts_to_zero :
      ∀ (i : ι), i ∈ s →
        h1RestrictionViaCocycles T (S i) x = 0)
    (gaugeIntoU_of_x_zero :
      x = 0 →
        ∃ q : B, ((a.gauge r).gauge (q : G)).ValuesIn U)
    (hU :
      ∀ z : NonabelianCocycle Γ G, z.ValuesIn U → z.IsCoboundary) :
    a.IsCoboundary := by
  have hx : x = 0 :=
    h1_eq_zero_of_gcd_one_restrictions T S s hgcd
      x_restricts_to_zero
  obtain ⟨q, hq⟩ := gaugeIntoU_of_x_zero hx
  have hcorrected :
      ((a.gauge r).gauge (q : G)).IsCoboundary :=
    hU _ hq
  have hgauged : (a.gauge r).IsCoboundary :=
    ((a.gauge r).isCoboundary_gauge_iff (q : G)).1 hcorrected
  exact (a.isCoboundary_gauge_iff r).1 hgauged

/-- The chosen-gauge coprime filtration supplies one gauge that is local on
every member of a generating subgroup family. -/
theorem NonabelianCocycle.exists_commonLocalGauge_of_chosen_gauge_subgroup_filtration_gcd_one_h1
    {k Γ : Type u} {G : Type v}
    [CommRing k] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G) (B U : Subgroup G)
    {ι : Type w} (T : Rep k Γ) (S : ι → Subgroup Γ)
    [∀ i, (S i).FiniteIndex]
    (s : Finset ι)
    (hgcd : s.gcd (fun i => (Nat.card (Γ ⧸ S i) : ℤ)) = 1)
    (hgen : (⨆ i, S i) = ⊤)
    (r : G) (hz : (a.gauge r).ValuesIn B)
    (x : groupCohomology.H1 T)
    (x_restricts_to_zero :
      ∀ (i : ι), i ∈ s →
        h1RestrictionViaCocycles T (S i) x = 0)
    (gaugeIntoU_of_x_zero :
      x = 0 →
        ∃ q : B, ((a.gauge r).gauge (q : G)).ValuesIn U)
    (hU :
      ∀ z : NonabelianCocycle Γ G, z.ValuesIn U → z.IsCoboundary) :
    ∃ b : G, ∀ i, a.IsLocalGauge (S i) b := by
  apply (isCoboundary_iff_exists_commonLocalGauge a S hgen).1
  exact a.isCoboundary_of_chosen_gauge_subgroup_filtration_gcd_one_h1
    B U T S s hgcd r hz x x_restricts_to_zero
      gaugeIntoU_of_x_zero hU

end RiemannResearch.GaloisCohomology
