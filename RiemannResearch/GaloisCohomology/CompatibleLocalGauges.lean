/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.LocalGaugeTransporter

/-!
# Compatible local gauges

A common gauge on a generating family of subgroups turns a nonabelian
one-cocycle into a global coboundary. The family-level form makes every
corresponding discrete nonabelian H¹ a subsingleton.

The motivating application is completion target B in the 5 August 2026 E8
Serre II memorandum. This module contains only the general cocycle argument;
the existence of compatible E8 gauges remains a separate open input. In
particular, subgroup generation and the separate existence of local gauges do
not imply the existence of one common gauge.

The fixed-point right-coset and anchored-correction equivalences below
formalize Section 7.2, Research Target 7.1, of the user-provided 13 August 2026
Serre II transporter manuscript. The source supports the statement and
terminology of those equivalences, not the asserted existence of a correction
for the thirty-one E8 survivor cases.
-/

universe u v w x

namespace RiemannResearch.GaloisCohomology

open NonabelianCocycle

/-- If a generating family of local restrictions admits one common gauge for
every selected cocycle, then every selected cocycle is a global coboundary.

The common-gauge hypothesis is the nonempty total intersection of the local
trivialization cosets; pairwise intersections alone are not asserted to
suffice. -/
theorem isCoboundary_of_compatibleLocalGauges
    {Γ : Type u} {G : Type v} {I : Type w}
    [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (Candidate : NonabelianCocycle Γ G → Prop)
    (H : I → Subgroup Γ) (hgen : (⨆ i, H i) = ⊤)
    (commonGauge :
      ∀ a, Candidate a → ∃ b, ∀ i, a.IsLocalGauge (H i) b) :
    ∀ a, Candidate a → a.IsCoboundary := by
  intro a ha
  obtain ⟨b, hb⟩ := commonGauge a ha
  refine ⟨b, ?_⟩
  apply eq_trivial_gauge_of_generating_family a b H hgen
  intro i σ hσ
  exact hb i σ hσ

namespace NonabelianCocycle

/-- The set of gauges which trivialize a cocycle on a subgroup. -/
def localGaugeSet
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G) (H : Subgroup Γ) : Set G :=
  {b | a.IsLocalGauge H b}

/-- The right coset through u of the subgroup of elements fixed by H.

Membership is written without first packaging the fixed elements as a
subgroup: b belongs exactly when b * u⁻¹ is fixed by H. -/
def fixedPointRightCoset
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (H : Subgroup Γ) (u : G) : Set G :=
  {b | IsFixedBy H (b * u⁻¹)}

/-- Literal right-coset description of fixedPointRightCoset. -/
theorem mem_fixedPointRightCoset_iff
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (H : Subgroup Γ) (u b : G) :
    b ∈ fixedPointRightCoset H u ↔
      ∃ k : G, IsFixedBy H k ∧ b = k * u := by
  constructor
  · intro hb
    refine ⟨b * u⁻¹, hb, ?_⟩
    simp [mul_assoc]
  · rintro ⟨k, hk, rfl⟩
    simpa [fixedPointRightCoset, mul_assoc] using hk

/-- Once u is a local gauge, all gauges on the same subgroup form its
fixed-point right coset. -/
theorem isLocalGauge_iff_mem_fixedPointRightCoset
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G) (H : Subgroup Γ) (u b : G)
    (hu : a.IsLocalGauge H u) :
    a.IsLocalGauge H b ↔ b ∈ fixedPointRightCoset H u := by
  constructor
  · intro hb
    change IsFixedBy H (b * u⁻¹)
    intro σ hσ
    have heq : b⁻¹ * (σ • b) = u⁻¹ * (σ • u) :=
      (hb σ hσ).symm.trans (hu σ hσ)
    have h := congrArg
      (fun x : G => b * x * (σ • u)⁻¹) heq
    have h' : (σ • b) * (σ • u)⁻¹ = b * u⁻¹ := by
      simpa [mul_assoc] using h
    simpa [smul_mul'] using h'
  · intro hb
    change IsFixedBy H (b * u⁻¹) at hb
    intro σ hσ
    have hfixed' : (σ • b) * (σ • u)⁻¹ = b * u⁻¹ := by
      simpa [smul_mul'] using hb σ hσ
    have h := congrArg
      (fun x : G => b⁻¹ * x * (σ • u)) hfixed'
    have heq : b⁻¹ * (σ • b) = u⁻¹ * (σ • u) := by
      simpa [mul_assoc] using h
    exact (hu σ hσ).trans heq.symm

/-- The set of gauges on a subgroup is the fixed-point right coset through any
chosen local gauge. -/
theorem localGaugeSet_eq_fixedPointRightCoset
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G) (H : Subgroup Γ) (u : G)
    (hu : a.IsLocalGauge H u) :
    localGaugeSet a H = fixedPointRightCoset H u := by
  ext b
  exact isLocalGauge_iff_mem_fixedPointRightCoset a H u b hu

/-- Anchored correction versus total fixed-point-coset intersection.

For any family of elements and any anchor, the existence of one anchored
fixed correction is exactly nonemptiness of the total right-coset
intersection. This is the purely group-theoretic equivalence displayed in
Research Target 7.1; no cocycle or generation hypothesis is needed. -/
theorem
    exists_anchoredFixedGaugeCorrection_iff_iInter_fixedPointRightCoset_nonempty
    {Γ : Type u} {G : Type v} {I : Type w}
    [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (H : I → Subgroup Γ) (u : I → G) (i₀ : I) :
    (∃ c₀ : G, ∀ i, IsFixedBy (H i) (transition u i i₀ * c₀)) ↔
      (⋂ i, fixedPointRightCoset (H i) (u i)).Nonempty := by
  constructor
  · rintro ⟨c₀, hc₀⟩
    refine ⟨c₀⁻¹ * u i₀, ?_⟩
    rw [Set.mem_iInter]
    intro i
    have hinv :
        IsFixedBy (H i) (transition u i i₀ * c₀)⁻¹ := by
      intro σ hσ
      calc
        σ • (transition u i i₀ * c₀)⁻¹ =
            (σ • (transition u i i₀ * c₀))⁻¹ :=
          smul_inv' σ (transition u i i₀ * c₀)
        _ = (transition u i i₀ * c₀)⁻¹ :=
          congrArg Inv.inv (hc₀ i σ hσ)
    simpa [fixedPointRightCoset, transition, mul_assoc] using hinv
  · rintro ⟨b, hb⟩
    refine ⟨u i₀ * b⁻¹, ?_⟩
    intro i
    have hi : b ∈ fixedPointRightCoset (H i) (u i) :=
      Set.mem_iInter.mp hb i
    change IsFixedBy (H i) (b * (u i)⁻¹) at hi
    have hinv : IsFixedBy (H i) (b * (u i)⁻¹)⁻¹ := by
      intro σ hσ
      calc
        σ • (b * (u i)⁻¹)⁻¹ = (σ • (b * (u i)⁻¹))⁻¹ :=
          smul_inv' σ (b * (u i)⁻¹)
        _ = (b * (u i)⁻¹)⁻¹ := congrArg Inv.inv (hi σ hσ)
    simpa [transition, mul_assoc] using hinv

/-- Research Target 7.1's three abstract formulations are equivalent:
global coboundary status, an anchored fixed correction, and nonemptiness of
the total fixed-point right-coset intersection.

This theorem proves the equivalence only. It does not assert that these
conditions hold for any of the thirty-one E8 survivor cases. -/
theorem isCoboundary_iff_iInter_fixedPointRightCoset_nonempty
    {Γ : Type u} {G : Type v} {I : Type w}
    [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G)
    (H : I → Subgroup Γ) (u : I → G) (i₀ : I)
    (hgen : (⨆ i, H i) = ⊤)
    (hlocal : ∀ i, a.IsLocalGauge (H i) (u i)) :
    a.IsCoboundary ↔
      (⋂ i, fixedPointRightCoset (H i) (u i)).Nonempty :=
  (isCoboundary_iff_exists_anchoredFixedGaugeCorrection
    a H u i₀ hgen hlocal).trans
    (exists_anchoredFixedGaugeCorrection_iff_iInter_fixedPointRightCoset_nonempty
      H u i₀)

end NonabelianCocycle

/-- **Exact common-gauge criterion for a generating family.**

A nonabelian cocycle is a global coboundary if and only if one element is a
local gauge on every subgroup in a generating family. This is the precise
logical content of the corrected common-gauge clause in Theorem 6.30 of the
user-provided Serre II manuscript: it characterizes common-gauge existence but
does not derive it from separately nonempty local-gauge sets.

Source: user-provided manuscript, corrected Theorem 6.30; the source supports
the statement and proof strategy.
-/
theorem isCoboundary_iff_exists_commonLocalGauge
    {Γ : Type u} {G : Type v} {I : Type w}
    [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G)
    (H : I → Subgroup Γ) (hgen : (⨆ i, H i) = ⊤) :
    a.IsCoboundary ↔ ∃ b, ∀ i, a.IsLocalGauge (H i) b := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro i σ hσ
    rw [hb]
    simp [NonabelianCocycle.trivial, NonabelianCocycle.gauge]
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply eq_trivial_gauge_of_generating_family a b H hgen
    intro i σ hσ
    exact hb i σ hσ

/-- **Total-intersection form of the exact common-gauge criterion.**

For a generating family, global coboundary status is equivalent to
nonemptiness of the total intersection of the local-gauge sets. Separate
nonemptiness of the individual sets is not enough.
-/
theorem isCoboundary_iff_iInter_localGaugeSet_nonempty
    {Γ : Type u} {G : Type v} {I : Type w}
    [Group Γ] [Group G] [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G)
    (H : I → Subgroup Γ) (hgen : (⨆ i, H i) = ⊤) :
    a.IsCoboundary ↔
      (⋂ i, NonabelianCocycle.localGaugeSet a (H i)).Nonempty := by
  rw [isCoboundary_iff_exists_commonLocalGauge a H hgen]
  simp only [Set.nonempty_iInter, NonabelianCocycle.localGaugeSet,
    Set.mem_ofPred_eq]

/-- If every cocycle in every member of a family admits one common gauge on a
generating family of subgroups, then each corresponding discrete nonabelian H¹
is a subsingleton. -/
theorem nonabelianH1_family_subsingleton_of_compatibleLocalGauges
    {S : Type u} (Γ : S → Type v) (G : S → Type w) (I : S → Type x)
    [∀ s, Group (Γ s)] [∀ s, Group (G s)]
    [∀ s, MulDistribMulAction (Γ s) (G s)]
    (H : ∀ s, I s → Subgroup (Γ s))
    (hgen : ∀ s, (⨆ i, H s i) = ⊤)
    (commonGauge :
      ∀ s (a : NonabelianCocycle (Γ s) (G s)),
        ∃ b, ∀ i, a.IsLocalGauge (H s i) b) :
    ∀ s, Subsingleton (NonabelianH1 (Γ s) (G s)) := by
  intro s
  constructor
  intro ξ η
  refine Quotient.inductionOn₂ ξ η ?_
  intro a b
  change NonabelianH1.classOf a = NonabelianH1.classOf b
  have ha : a.IsCoboundary :=
    isCoboundary_of_compatibleLocalGauges (fun _ => True) (H s) (hgen s)
      (fun c _ => commonGauge s c) a trivial
  have hb : b.IsCoboundary :=
    isCoboundary_of_compatibleLocalGauges (fun _ => True) (H s) (hgen s)
      (fun c _ => commonGauge s c) b trivial
  exact
    (NonabelianH1.classOf_eq_neutral_iff_isCoboundary a).2 ha |>.trans
      ((NonabelianH1.classOf_eq_neutral_iff_isCoboundary b).2 hb).symm

end RiemannResearch.GaloisCohomology
