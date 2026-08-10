/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.CompatibleLocalGauges
import RiemannResearch.GroupTheory.GeneratedSubgroupsOfCoprimeIndex

/-!
# Full-Weyl generating family and common-gauge criterion

This module packages the corrected abstract content of Theorem 6.30 in the
user-provided Serre II manuscript. The gcd-one orbit degrees imply generation
of the projective subgroup family, and full inverse images generate the lifted
group. Global neutrality is then equivalent to nonemptiness of the total
intersection of local-gauge sets.

The theorem does not infer total-intersection nonemptiness from separate
nonemptiness of the individual local-gauge sets. That simultaneous
compatibility remains the E8-specific input.

Source: user-provided manuscript, corrected Theorem 6.30; the source supports
the statement and proof strategy.
-/

universe u v w x

namespace RiemannResearch.E8

open RiemannResearch.GaloisCohomology

/-- **Corrected abstract Theorem 6.30.**

A gcd-one family of projective subgroups generates the projective group, its
full inverse images under a surjective quotient map generate the covering
group, and global coboundary status is exactly nonemptiness of the total
intersection of the lifted local-gauge sets.

The conclusion is an equivalence with intersection nonemptiness, not a proof
of that nonemptiness.
-/
theorem correctedTheorem630
    {J : Type u} {Γ : Type v} {G : Type w} {I : Type x}
    [Group J] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    [Nonempty I]
    (π : Γ →* J) (hπ : Function.Surjective π)
    (D : I → Subgroup J)
    (hgcd : Nat.setGcd (Set.range fun i => (D i).index) = 1)
    (a : NonabelianCocycle Γ G) :
    (⨆ i, D i) = ⊤ ∧
      (⨆ i, (D i).comap π) = ⊤ ∧
        (a.IsCoboundary ↔
          (⋂ i, a.localGaugeSet ((D i).comap π)).Nonempty) := by
  have hprojective : (⨆ i, D i) = ⊤ :=
    RiemannResearch.GroupTheory.iSup_eq_top_of_setGcd_indices D hgcd
  have hlifted : (⨆ i, (D i).comap π) = ⊤ :=
    RiemannResearch.GroupTheory.iSup_comap_eq_top_of_surjective
      π hπ D hprojective
  exact ⟨hprojective, hlifted,
    isCoboundary_iff_iInter_localGaugeSet_nonempty
      a (fun i => (D i).comap π) hlifted⟩

end RiemannResearch.E8
