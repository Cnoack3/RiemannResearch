/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import RiemannResearch.GaloisCohomology.SubgroupGaugeFiltration

/-!
# Additive H¹ and nonabelian quotient cocycles

This module connects a nonabelian cocycle with coefficients in a group Q to
Mathlib's additive first cohomology whenever Q is equivariantly
multiplicatively equivalent to the additive group underlying a representation
T. It proves that the resulting additive H¹ class vanishes exactly when the
original nonabelian cocycle is a coboundary, and packages additive H¹ vanishing
as a constructor for SubgroupGaugeFiltration.

The construction is purely an interface theorem. Applications must still
construct the concrete quotient equivalence, prove its action compatibility,
and establish H¹ vanishing for the representation.

Source:
* Mathlib,
  RepresentationTheory.Homological.GroupCohomology.LowDegree, for the
  definitions of additive one-cocycles, coboundaries, and the quotient map to
  H¹:
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean
* User-provided quotient-H¹ gauge-filtration continuation handoff
  (25 August 2026), for the bridge and filtration application.
-/

universe u v

namespace RiemannResearch.GaloisCohomology

open CategoryTheory

namespace NonabelianCocycle

variable {k Γ : Type u} {Q : Type v}
variable [CommRing k] [Group Γ] [Group Q] [MulDistribMulAction Γ Q]

/-- Transport a nonabelian cocycle through an equivariant multiplicative
equivalence with the additive group of a representation.

The commutativity needed to reverse the order in Mathlib's additive cocycle
convention is supplied by the additive group underlying T. -/
def toAdditiveCocycle₁
    (T : Rep k Γ) (e : Q ≃* Multiplicative T)
    (hρ : ∀ (σ : Γ) (q : Q),
      (e (σ • q)).toAdd = T.ρ σ (e q).toAdd)
    (a : NonabelianCocycle Γ Q) :
    groupCohomology.cocycles₁ T := by
  refine ⟨fun σ => (e (a σ)).toAdd, ?_⟩
  apply (groupCohomology.mem_cocycles₁_iff (A := T) _).2
  intro σ τ
  have h := congrArg (fun q => (e q).toAdd) (a.map_mul' σ τ)
  simpa [hρ, add_comm] using h

/-- The additive H¹ class associated to a nonabelian cocycle through an
equivariant multiplicative equivalence. -/
noncomputable def additiveH1Class
    (T : Rep k Γ) (e : Q ≃* Multiplicative T)
    (hρ : ∀ (σ : Γ) (q : Q),
      (e (σ • q)).toAdd = T.ρ σ (e q).toAdd)
    (a : NonabelianCocycle Γ Q) :
    groupCohomology.H1 T :=
  ConcreteCategory.hom (groupCohomology.H1π T)
    (toAdditiveCocycle₁ T e hρ a)

/-- Under an equivariant multiplicative equivalence with the additive group of
a representation, the transported additive H¹ class is zero exactly when the
original nonabelian cocycle is a coboundary. -/
theorem additiveH1Class_eq_zero_iff_isCoboundary
    (T : Rep k Γ) (e : Q ≃* Multiplicative T)
    (hρ : ∀ (σ : Γ) (q : Q),
      (e (σ • q)).toAdd = T.ρ σ (e q).toAdd)
    (a : NonabelianCocycle Γ Q) :
    additiveH1Class T e hρ a = 0 ↔ a.IsCoboundary := by
  rw [additiveH1Class, groupCohomology.H1π_eq_zero_iff]
  constructor
  · intro hmem
    change
      (toAdditiveCocycle₁ T e hρ a : Γ → T) ∈
        (ModuleCat.Hom.hom (groupCohomology.d₀₁ T)).range at hmem
    obtain ⟨x, hx⟩ := hmem
    refine ⟨e.symm (Multiplicative.ofAdd x), ?_⟩
    ext σ
    apply e.injective
    change (e (a σ)).toAdd =
      (e ((NonabelianCocycle.trivial.gauge
        (e.symm (Multiplicative.ofAdd x))) σ)).toAdd
    have hxσ := congrFun hx σ
    simpa [toAdditiveCocycle₁, NonabelianCocycle.gauge,
      NonabelianCocycle.trivial, groupCohomology.d₀₁_hom_apply,
      hρ, sub_eq_add_neg, add_comm] using hxσ.symm
  · rintro ⟨q, hq⟩
    change
      (toAdditiveCocycle₁ T e hρ a : Γ → T) ∈
        (ModuleCat.Hom.hom (groupCohomology.d₀₁ T)).range
    refine ⟨(e q).toAdd, ?_⟩
    funext σ
    have hσ := congrArg (fun z => (e (z σ)).toAdd) hq
    simpa [toAdditiveCocycle₁, NonabelianCocycle.gauge,
      NonabelianCocycle.trivial, groupCohomology.d₀₁_hom_apply,
      hρ, sub_eq_add_neg, add_comm] using hσ.symm

/-- Vanishing of the whole additive H¹ module neutralizes every nonabelian
cocycle in an equivariantly equivalent coefficient group. -/
theorem all_isCoboundary_of_additiveH1_eq_zero
    (T : Rep k Γ) (e : Q ≃* Multiplicative T)
    (hρ : ∀ (σ : Γ) (q : Q),
      (e (σ • q)).toAdd = T.ρ σ (e q).toAdd)
    (hH1 : ∀ x : groupCohomology.H1 T, x = 0) :
    ∀ a : NonabelianCocycle Γ Q, a.IsCoboundary := by
  intro a
  exact (additiveH1Class_eq_zero_iff_isCoboundary T e hρ a).1
    (hH1 (additiveH1Class T e hρ a))

end NonabelianCocycle

/-- Extend a subgroup gauge filtration by a quotient whose coefficient group
is equivariantly equivalent to the additive group of a representation with
vanishing H¹. -/
def SubgroupGaugeFiltration.stepOfAdditiveQuotientH1
    {k Γ : Type u} {G : Type v}
    [CommRing k] [Group Γ] [Group G] [MulDistribMulAction Γ G]
    {U V : Subgroup G} [MulDistribMulAction Γ U]
    (hU : ∀ (σ : Γ) (u : U), ((σ • u : U) : G) = σ • (u : G))
    (N : Subgroup U) [N.Normal]
    [MulDistribMulAction Γ (U ⧸ N)]
    (hquot : ∀ (σ : Γ) (u : U),
      QuotientGroup.mk' N (σ • u) = σ • QuotientGroup.mk' N u)
    (hN : ∀ u : U, u ∈ N ↔ (u : G) ∈ V)
    (T : Rep k Γ) (e : (U ⧸ N) ≃* Multiplicative T)
    (hρ : ∀ (σ : Γ) (q : U ⧸ N),
      (e (σ • q)).toAdd = T.ρ σ (e q).toAdd)
    (hH1 : ∀ x : groupCohomology.H1 T, x = 0)
    (tail : SubgroupGaugeFiltration Γ G V) :
    SubgroupGaugeFiltration Γ G U :=
  SubgroupGaugeFiltration.stepOfQuotientH1 hU N hquot hN
    (NonabelianCocycle.all_isCoboundary_of_additiveH1_eq_zero
      T e hρ hH1)
    tail

end RiemannResearch.GaloisCohomology
