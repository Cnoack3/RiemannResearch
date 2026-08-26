/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.SubgroupFiltration

/-!
# Finite gauge-lowering filtrations

A finite sequence of subgroup-valued gauge corrections ending in the trivial
subgroup neutralizes every cocycle valued in its first subgroup. This is the
purely nonabelian induction underlying a unipotent height-filtration argument.

Each step records the genuinely local input: a cocycle valued in the current
subgroup can be gauged, by an element of that subgroup, into the next one. The
terminal case is proved rather than assumed because a cocycle valued in the
trivial subgroup is the trivial cocycle.
-/

universe u v

namespace RiemannResearch.GaloisCohomology

/-- A finite gauge-lowering filtration from a coefficient subgroup to the
trivial subgroup. -/
inductive SubgroupGaugeFiltration
    (Γ : Type u) (G : Type v)
    [Group Γ] [Group G] [MulDistribMulAction Γ G] :
    Subgroup G → Type (max u v)
  | bottom : SubgroupGaugeFiltration Γ G (⊥ : Subgroup G)
  | step {U : Subgroup G} (V : Subgroup G)
      (lower :
        ∀ z : NonabelianCocycle Γ G, z.ValuesIn U →
          ∃ q : U, (z.gauge (q : G)).ValuesIn V)
      (tail : SubgroupGaugeFiltration Γ G V) :
      SubgroupGaugeFiltration Γ G U

namespace SubgroupGaugeFiltration

/-- Extend a gauge filtration by one step when the quotient coefficient group
has neutral nonabelian H¹.

The quotient kernel is presented as a normal subgroup N of the subtype group
U; hN identifies it with the ambient next subgroup V. -/
def stepOfQuotientH1
    {Γ : Type u} {G : Type v}
    [Group Γ] [Group G] [MulDistribMulAction Γ G]
    {U V : Subgroup G}
    [MulDistribMulAction Γ U]
    (hU : ∀ (σ : Γ) (u : U),
      ((σ • u : U) : G) = σ • (u : G))
    (N : Subgroup U) [N.Normal]
    [MulDistribMulAction Γ (U ⧸ N)]
    (hquot : ∀ (σ : Γ) (u : U),
      QuotientGroup.mk' N (σ • u) =
        σ • QuotientGroup.mk' N u)
    (hN : ∀ u : U, u ∈ N ↔ (u : G) ∈ V)
    (hH1 : ∀ b : NonabelianCocycle Γ (U ⧸ N),
      b.IsCoboundary)
    (tail : SubgroupGaugeFiltration Γ G V) :
    SubgroupGaugeFiltration Γ G U :=
  .step V
    (fun a ha =>
      a.exists_subgroupGauge_valuesIn_of_quotient_h1
        U V hU N hquot hN hH1 ha)
    tail

/-- Every cocycle valued in the first subgroup of a finite gauge-lowering
filtration is a coboundary. -/
theorem isCoboundary
    {Γ : Type u} {G : Type v}
    [Group Γ] [Group G] [MulDistribMulAction Γ G] :
    ∀ {U : Subgroup G}, SubgroupGaugeFiltration Γ G U →
      ∀ z : NonabelianCocycle Γ G, z.ValuesIn U → z.IsCoboundary
  | _, .bottom, z, hz => by
      refine ⟨1, ?_⟩
      rw [NonabelianCocycle.gauge_one]
      apply NonabelianCocycle.ext
      intro σ
      exact Subgroup.mem_bot.mp (hz σ)
  | _, .step V lower tail, z, hz => by
      obtain ⟨q, hq⟩ := lower z hz
      have hcorrected : (z.gauge (q : G)).IsCoboundary :=
        tail.isCoboundary _ hq
      exact (z.isCoboundary_gauge_iff (q : G)).1 hcorrected

end SubgroupGaugeFiltration

end RiemannResearch.GaloisCohomology
