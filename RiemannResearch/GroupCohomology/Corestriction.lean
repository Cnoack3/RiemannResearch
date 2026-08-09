/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import RiemannResearch.CategoryTheory.PreadditiveIsoConjugation
import RiemannResearch.GroupCohomology.ExplicitRestriction
import RiemannResearch.LinearAlgebra.QuotientMap

/-!
# Corestriction in additive first group cohomology

This file constructs the quotient-transversal cochain underlying
corestriction for a normal finite-index subgroup.

Corestriction after restriction is multiplication by the subgroup index.
In the opposite order, restriction after corestriction is a norm, not
multiplication by the index on arbitrary subgroup classes.
-/

open CategoryTheory
open scoped BigOperators

universe u

namespace RiemannResearch.GroupCohomology

/-- A chosen representative of each coset of a normal subgroup. -/
noncomputable def quotientRepresentative
    {G : Type u} [Group G] (S : Subgroup G) [S.Normal] :
    G ⧸ S → G :=
  Function.surjInv (QuotientGroup.mk'_surjective S)

theorem quotientRepresentative_spec
    {G : Type u} [Group G] (S : Subgroup G) [S.Normal]
    (q : G ⧸ S) :
    QuotientGroup.mk' S (quotientRepresentative S q) = q :=
  Function.rightInverse_surjInv (QuotientGroup.mk'_surjective S) q

/-- The subgroup-valued defect of the chosen quotient representatives. -/
noncomputable def quotientDefect
    {G : Type u} [Group G] (S : Subgroup G) [S.Normal]
    (g : G) (q : G ⧸ S) : S :=
  ⟨(quotientRepresentative S (QuotientGroup.mk' S g * q))⁻¹ *
      g * quotientRepresentative S q, by
    have hmem :
        (quotientRepresentative S (QuotientGroup.mk' S g * q))⁻¹ *
          g * quotientRepresentative S q ∈
            (QuotientGroup.mk' S).ker := by
      change QuotientGroup.mk' S
        ((quotientRepresentative S (QuotientGroup.mk' S g * q))⁻¹ *
          g * quotientRepresentative S q) = 1
      rw [map_mul, map_mul, map_inv, quotientRepresentative_spec,
        quotientRepresentative_spec]
      simp
    rwa [QuotientGroup.ker_mk' S] at hmem⟩

@[simp]
theorem coe_quotientDefect
    {G : Type u} [Group G] (S : Subgroup G) [S.Normal]
    (g : G) (q : G ⧸ S) :
    ((quotientDefect S g q : S) : G) =
      (quotientRepresentative S (QuotientGroup.mk' S g * q))⁻¹ *
        g * quotientRepresentative S q :=
  rfl

theorem quotientRepresentative_mul_defect
    {G : Type u} [Group G] (S : Subgroup G) [S.Normal]
    (g : G) (q : G ⧸ S) :
    quotientRepresentative S (QuotientGroup.mk' S g * q) *
        (quotientDefect S g q : G) =
      g * quotientRepresentative S q := by
  simp [quotientDefect, mul_assoc]

theorem quotientDefect_mul
    {G : Type u} [Group G] (S : Subgroup G) [S.Normal]
    (g h : G) (q : G ⧸ S) :
    quotientDefect S (g * h) q =
      quotientDefect S g (QuotientGroup.mk' S h * q) *
        quotientDefect S h q := by
  apply Subtype.ext
  simp [quotientDefect, mul_assoc]

/-- One summand in the normal-subgroup corestriction formula. -/
noncomputable def normalCorestrictionSummand
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal]
    (z : S → A) (g : G) (q : G ⧸ S) : A :=
  (A.ρ (quotientRepresentative S
    (QuotientGroup.mk' S g * q))) (z (quotientDefect S g q))

/-- The quotient-transversal corestriction formula on additive one-cochains. -/
noncomputable def normalCorestrictionCochain
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex]
    (z : S → A) (g : G) : A := by
  letI := Fintype.ofFinite (G ⧸ S)
  exact ∑ q : G ⧸ S, normalCorestrictionSummand A S z g q

/-- The corestriction formula is linear on one-cochains. -/
noncomputable def normalCorestrictionCochainLinearMap
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex] :
    (S → A) →ₗ[k] (G → A) where
  toFun := normalCorestrictionCochain A S
  map_add' := by
    intro z w
    funext g
    simp [normalCorestrictionCochain, normalCorestrictionSummand,
      Finset.sum_add_distrib]
  map_smul' := by
    intro c z
    funext g
    simp only [normalCorestrictionCochain, normalCorestrictionSummand,
      Pi.smul_apply, map_smul]
    rw [Finset.smul_sum]
    simp

theorem normalCorestrictionSummand_mul
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal]
    (z : groupCohomology.cocycles₁ (Rep.res S.subtype A))
    (g h : G) (q : G ⧸ S) :
    normalCorestrictionSummand A S z (g * h) q =
      (A.ρ g) (normalCorestrictionSummand A S z h q) +
        normalCorestrictionSummand A S z g
          (QuotientGroup.mk' S h * q) := by
  have hz :
      ∀ a b : S, z (a * b) =
        ((Rep.res S.subtype A).ρ a) (z b) + z a :=
    (groupCohomology.mem_cocycles₁_iff
      (A := Rep.res S.subtype A) z).mp z.property
  unfold normalCorestrictionSummand
  rw [quotientDefect_mul, hz, map_add]
  simp only [map_mul, mul_assoc]
  congr 1
  change
    (A.ρ (quotientRepresentative S
      (QuotientGroup.mk' S g *
        (QuotientGroup.mk' S h * q))))
      ((A.ρ (quotientDefect S g
        (QuotientGroup.mk' S h * q) : G))
        (z (quotientDefect S h q))) =
      (A.ρ g)
        ((A.ρ (quotientRepresentative S
          (QuotientGroup.mk' S h * q)))
          (z (quotientDefect S h q)))
  rw [← Module.End.mul_apply, ← map_mul,
    quotientRepresentative_mul_defect, map_mul, Module.End.mul_apply]

/-- The quotient-transversal corestriction formula sends additive one-cocycles
on the normal subgroup to additive one-cocycles on the ambient group. -/
theorem normalCorestrictionCochain_mem_cocycles₁
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex]
    (z : groupCohomology.cocycles₁ (Rep.res S.subtype A)) :
    normalCorestrictionCochain A S z ∈
      groupCohomology.cocycles₁ A := by
  classical
  let _ := Fintype.ofFinite (G ⧸ S)
  apply (groupCohomology.mem_cocycles₁_iff
    (normalCorestrictionCochain A S z)).2
  intro g h
  simp only [normalCorestrictionCochain]
  simp_rw [normalCorestrictionSummand_mul]
  rw [Finset.sum_add_distrib, map_sum]
  congr 1
  simpa using
    (Equiv.sum_comp
      (Equiv.mulLeft (QuotientGroup.mk' S h))
      (fun q : G ⧸ S => normalCorestrictionSummand A S z g q))

/-- The zero-cochain whose coboundary is the corestriction of a
coboundary. -/
noncomputable def normalCorestrictionPotential
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex]
    (x : A) : A := by
  letI := Fintype.ofFinite (G ⧸ S)
  exact ∑ q : G ⧸ S, (A.ρ (quotientRepresentative S q)) x

/-- Corestriction of the coboundary of a zero-cochain is the coboundary
of its transferred potential. -/
theorem normalCorestrictionCochain_d₀₁_apply
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex]
    (x : A) (g : G) :
    normalCorestrictionCochain A S
        ((groupCohomology.d₀₁ (Rep.res S.subtype A)).hom x) g =
      (groupCohomology.d₀₁ A).hom
        (normalCorestrictionPotential A S x) g := by
  classical
  let _ := Fintype.ofFinite (G ⧸ S)
  unfold normalCorestrictionCochain normalCorestrictionPotential
    normalCorestrictionSummand
  simp only [groupCohomology.d₀₁_hom_apply, MonoidHom.comp_apply, map_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [← Module.End.mul_apply, ← map_mul]
    change
      (A.ρ (quotientRepresentative S (QuotientGroup.mk' S g * q) *
        (quotientDefect S g q : G))) x =
        (A.ρ g) ((A.ρ (quotientRepresentative S q)) x)
    rw [quotientRepresentative_mul_defect, map_mul, Module.End.mul_apply]
  · simpa using
      (Equiv.sum_comp
        (Equiv.mulLeft (QuotientGroup.mk' S g))
        (fun q : G ⧸ S => (A.ρ (quotientRepresentative S q)) x))

/-- The normal finite-index corestriction formula sends additive
one-coboundaries on the subgroup to additive one-coboundaries on the
ambient group. -/
theorem normalCorestrictionCochain_mem_coboundaries₁
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex]
    (z : groupCohomology.coboundaries₁ (Rep.res S.subtype A)) :
    normalCorestrictionCochain A S z ∈
      groupCohomology.coboundaries₁ A := by
  rcases z.property with ⟨x, hx⟩
  refine ⟨normalCorestrictionPotential A S x, ?_⟩
  funext g
  rw [show (z : S → A) =
    (groupCohomology.d₀₁ (Rep.res S.subtype A)).hom x from hx.symm]
  exact (normalCorestrictionCochain_d₀₁_apply A S x g).symm

/-- The normal corestriction cochain map restricted to additive
one-cocycles. -/
noncomputable def normalCorestrictionCocyclesLinearMap
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex] :
    groupCohomology.cocycles₁ (Rep.res S.subtype A) →ₗ[k]
      groupCohomology.cocycles₁ A :=
  (normalCorestrictionCochainLinearMap A S).restrict
    (fun z hz =>
      normalCorestrictionCochain_mem_cocycles₁ A S ⟨z, hz⟩)

/-- The cocycle-level normal corestriction map sends the range of the
subgroup coboundary map into the range of the ambient coboundary map. -/
theorem normalCorestrictionCocyclesLinearMap_maps_toCyclesRange
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex] :
    (groupCohomology.shortComplexH1
      (Rep.res S.subtype A)).moduleCatToCycles.range ≤
      Submodule.comap (normalCorestrictionCocyclesLinearMap A S)
        (groupCohomology.shortComplexH1 A).moduleCatToCycles.range := by
  intro z hz
  rcases hz with ⟨x, rfl⟩
  refine ⟨normalCorestrictionPotential A S x, ?_⟩
  apply groupCohomology.cocycles₁_ext
  intro g
  exact (normalCorestrictionCochain_d₀₁_apply A S x g).symm

/-- The map on explicit left-homology quotients induced by normal
corestriction. -/
noncomputable def normalCorestrictionLeftHomologyLinearMap
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex] :
    ((groupCohomology.shortComplexH1
      (Rep.res S.subtype A)).moduleCatLeftHomologyData.H : Type u) →ₗ[k]
      ((groupCohomology.shortComplexH1 A).moduleCatLeftHomologyData.H :
        Type u) :=
  Submodule.mapQ
    (groupCohomology.shortComplexH1
      (Rep.res S.subtype A)).moduleCatToCycles.range
    (groupCohomology.shortComplexH1 A).moduleCatToCycles.range
    (normalCorestrictionCocyclesLinearMap A S)
    (normalCorestrictionCocyclesLinearMap_maps_toCyclesRange A S)

/-- Normal corestriction as a morphism between the explicit left-homology
objects computing additive first group cohomology. -/
noncomputable def normalCorestrictionLeftHomology
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex] :
    (groupCohomology.shortComplexH1
      (Rep.res S.subtype A)).moduleCatLeftHomologyData.H ⟶
      (groupCohomology.shortComplexH1 A).moduleCatLeftHomologyData.H :=
  ModuleCat.ofHom (normalCorestrictionLeftHomologyLinearMap A S)

/-- Corestriction on additive first group cohomology for a normal
finite-index subgroup.

This construction is additive. It is not a corestriction on pointed
nonabelian first cohomology. -/
noncomputable def h1Corestriction
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex] :
    groupCohomology.H1 (Rep.res S.subtype A) ⟶
      groupCohomology.H1 A :=
  (groupCohomology.H1Iso (Rep.res S.subtype A)).hom ≫
    normalCorestrictionLeftHomology A S ≫
      (groupCohomology.H1Iso A).inv

/-- The zero-cochain measuring the difference between corestriction after
restriction and multiplication by the subgroup index. -/
noncomputable def normalCorestrictionRestrictionPotential
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex]
    (z : groupCohomology.cocycles₁ A) : A := by
  letI := Fintype.ofFinite (G ⧸ S)
  exact ∑ q : G ⧸ S, z (quotientRepresentative S q)

/-- A normal-corestriction summand of a restricted ambient cocycle,
expanded using the ambient cocycle identity. -/
theorem normalCorestrictionSummand_restrict
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal]
    (z : groupCohomology.cocycles₁ A) (g : G) (q : G ⧸ S) :
    normalCorestrictionSummand A S (fun s : S => z s.1) g q =
      (A.ρ g) (z (quotientRepresentative S q)) + z g -
        z (quotientRepresentative S (QuotientGroup.mk' S g * q)) := by
  have hz : ∀ a b : G, z (a * b) = (A.ρ a) (z b) + z a :=
    (groupCohomology.mem_cocycles₁_iff (A := A) z).mp z.property
  have h := hz
    (quotientRepresentative S (QuotientGroup.mk' S g * q))
    (quotientDefect S g q : G)
  rw [quotientRepresentative_mul_defect] at h
  rw [hz g (quotientRepresentative S q)] at h
  unfold normalCorestrictionSummand
  exact (eq_sub_iff_add_eq).2 h.symm

/-- On additive one-cocycles, corestriction after restriction differs from
multiplication by the subgroup index by an explicit coboundary. -/
theorem normalCorestrictionCochain_restrict_apply
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex]
    (z : groupCohomology.cocycles₁ A) (g : G) :
    normalCorestrictionCochain A S (fun s : S => z s.1) g =
      (Nat.card (G ⧸ S)) • z g +
        (ModuleCat.Hom.hom (groupCohomology.d₀₁ A))
          (normalCorestrictionRestrictionPotential A S z) g := by
  classical
  let _ := Fintype.ofFinite (G ⧸ S)
  unfold normalCorestrictionCochain normalCorestrictionRestrictionPotential
  simp_rw [normalCorestrictionSummand_restrict]
  simp only [groupCohomology.d₀₁_hom_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, map_sum,
    Finset.sum_const, Finset.card_univ]
  have hperm :
      (∑ x : G ⧸ S,
        z (quotientRepresentative S (QuotientGroup.mk' S g * x))) =
      ∑ x : G ⧸ S, z (quotientRepresentative S x) := by
    simpa using
      (Equiv.sum_comp
        (Equiv.mulLeft (QuotientGroup.mk' S g))
        (fun x : G ⧸ S => z (quotientRepresentative S x)))
  rw [hperm, Nat.card_eq_fintype_card]
  abel

/-- On explicit left-homology quotient modules, restriction followed by
normal corestriction is multiplication by the subgroup index. -/
theorem normalCorestrictionLeftHomologyLinearMap_comp_restriction
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex] :
    (normalCorestrictionLeftHomologyLinearMap A S).comp
      (restrictionLeftHomologyLinearMap A S) =
        Nat.card (G ⧸ S) • LinearMap.id := by
  apply RiemannResearch.LinearAlgebra.mapQ_comp_eq_nsmul_id
  intro z
  change groupCohomology.cocycles₁ A at z
  refine ⟨normalCorestrictionRestrictionPotential A S z, ?_⟩
  apply groupCohomology.cocycles₁_ext
  intro g
  change
    (ModuleCat.Hom.hom (groupCohomology.d₀₁ A))
        (normalCorestrictionRestrictionPotential A S z) g =
      normalCorestrictionCochain A S (fun s : S => z s.1) g -
        Nat.card (G ⧸ S) • z g
  rw [normalCorestrictionCochain_restrict_apply]
  abel

/-- On the explicit left-homology objects, restriction followed by normal
corestriction is multiplication by the subgroup index. -/
theorem restrictionLeftHomology_comp_normalCorestriction
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex] :
    restrictionLeftHomology A S ≫
      normalCorestrictionLeftHomology A S =
        Nat.card (G ⧸ S) •
          𝟙 (groupCohomology.shortComplexH1 A).moduleCatLeftHomologyData.H := by
  ext x
  change
    (normalCorestrictionLeftHomologyLinearMap A S)
        (restrictionLeftHomologyLinearMap A S x) =
      Nat.card (G ⧸ S) • x
  exact LinearMap.congr_fun
    (normalCorestrictionLeftHomologyLinearMap_comp_restriction A S) x

/-- Restriction followed by corestriction is multiplication by the subgroup
index on additive first group cohomology. -/
theorem h1RestrictionViaCocycles_comp_h1Corestriction
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] [S.FiniteIndex] :
    h1RestrictionViaCocycles A S ≫ h1Corestriction A S =
      Nat.card (G ⧸ S) • 𝟙 (groupCohomology.H1 A) := by
  apply RiemannResearch.CategoryTheory.isoConjugate_comp_eq_nsmul_id
  exact restrictionLeftHomology_comp_normalCorestriction A S

end RiemannResearch.GroupCohomology
