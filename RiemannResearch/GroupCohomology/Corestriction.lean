/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

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

end RiemannResearch.GroupCohomology
