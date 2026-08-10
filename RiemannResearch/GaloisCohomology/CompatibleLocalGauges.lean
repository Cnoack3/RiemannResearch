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
