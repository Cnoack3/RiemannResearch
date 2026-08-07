/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GroupCohomology.Restriction

/-!
# Conjugation in additive first group cohomology

This module constructs the additive H¹ isomorphism associated with conjugating
a subgroup, its raw functorial composition law, and the group-homomorphism
square underlying compatibility with restriction.
-/

open CategoryTheory

universe u

namespace RiemannResearch.GroupCohomology

/-- The conjugate subgroup g H g⁻¹. -/
def conjugateSubgroup {G : Type u} [Group G]
    (H : Subgroup G) (g : G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

/-- Conjugation by g as an isomorphism from H to g H g⁻¹. -/
noncomputable def conjugateEquiv {G : Type u} [Group G]
    (H : Subgroup G) (g : G) :
    H ≃* conjugateSubgroup H g := by
  unfold conjugateSubgroup
  exact H.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulEquiv.injective _)

@[simp]
theorem coe_conjugateEquiv {G : Type u} [Group G]
    (H : Subgroup G) (g : G) (h : H) :
    ((conjugateEquiv H g h : conjugateSubgroup H g) : G) =
      g * (h : G) * g⁻¹ := by
  rfl

@[simp]
theorem coe_conjugateEquiv_symm {G : Type u} [Group G]
    (H : Subgroup G) (g : G) (x : conjugateSubgroup H g) :
    (((conjugateEquiv H g).symm x : H) : G) =
      g⁻¹ * (x : G) * g := by
  have hx := congrArg Subtype.val
    ((conjugateEquiv H g).apply_symm_apply x)
  change g * (((conjugateEquiv H g).symm x : H) : G) * g⁻¹ =
    (x : G) at hx
  calc
    (((conjugateEquiv H g).symm x : H) : G) =
        g⁻¹ * (g * (((conjugateEquiv H g).symm x : H) : G) * g⁻¹) *
          g := by
            simp [mul_assoc]
    _ = g⁻¹ * (x : G) * g := by rw [hx]

@[simp]
theorem conjugateSubgroup_one {G : Type u} [Group G]
    (H : Subgroup G) :
    conjugateSubgroup H 1 = H := by
  ext x
  simp [conjugateSubgroup]

/-- Successive conjugation by g and then h conjugates by h * g. -/
theorem conjugateSubgroup_mul {G : Type u} [Group G]
    (H : Subgroup G) (g h : G) :
    conjugateSubgroup (conjugateSubgroup H g) h =
      conjugateSubgroup H (h * g) := by
  unfold conjugateSubgroup
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- Conjugation preserves subgroup inclusions. -/
theorem conjugateSubgroup_mono
    {G : Type u} [Group G] {K H : Subgroup G}
    (hKH : K ≤ H) (g : G) :
    conjugateSubgroup K g ≤ conjugateSubgroup H g :=
  Subgroup.map_mono hKH

/-- The action of a group element on the coefficient module. -/
noncomputable def actionLinearEquiv
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (g : G) : A ≃ₗ[k] A :=
  LinearEquiv.mk (A.ρ g) (A.ρ g⁻¹)
    (by
      intro x
      change (A.ρ g⁻¹) ((A.ρ g) x) = x
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply])
    (by
      intro x
      change (A.ρ g) ((A.ρ g⁻¹) x) = x
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply])

/-- The coefficient intertwiner used by subgroup conjugation. -/
noncomputable def conjugationHom
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (H : Subgroup G) (g : G) :
    Rep.res (conjugateEquiv H g).symm.toMonoidHom
        (Rep.res H.subtype A) ⟶
      Rep.res (conjugateSubgroup H g).subtype A :=
  Rep.ofHom
    { toLinearMap := (actionLinearEquiv A g).toLinearMap
      isIntertwining' := by
        intro x
        ext v
        simp [actionLinearEquiv, mul_assoc] }

/-- Conjugation from H¹(H,A) to H¹(g H g⁻¹,A). -/
noncomputable def h1Conjugation
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (H : Subgroup G) (g : G) :
    groupCohomology.H1 (Rep.res H.subtype A) ⟶
      groupCohomology.H1
        (Rep.res (conjugateSubgroup H g).subtype A) :=
  groupCohomology.map (conjugateEquiv H g).symm.toMonoidHom
    (conjugationHom A H g) 1

/-- Conjugation is an isomorphism on additive H¹. -/
noncomputable def h1ConjugationIso
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (H : Subgroup G) (g : G) :
    groupCohomology.H1 (Rep.res H.subtype A) ≅
      groupCohomology.H1
        (Rep.res (conjugateSubgroup H g).subtype A) :=
  groupCohomology.mapIso (conjugateEquiv H g)
    (actionLinearEquiv A g) (by
      intro h
      ext x
      simp [actionLinearEquiv, mul_assoc]) 1

theorem h1Conjugation_eq_iso_hom
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (H : Subgroup G) (g : G) :
    h1Conjugation A H g = (h1ConjugationIso A H g).hom := by
  unfold h1Conjugation h1ConjugationIso
  rw [groupCohomology.mapIso_hom]
  rfl

@[simp]
theorem h1Conjugation_hom_inv
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (H : Subgroup G) (g : G) :
    h1Conjugation A H g ≫ (h1ConjugationIso A H g).inv = 𝟙 _ := by
  rw [h1Conjugation_eq_iso_hom]
  exact (h1ConjugationIso A H g).hom_inv_id

@[simp]
theorem h1Conjugation_inv_hom
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (H : Subgroup G) (g : G) :
    (h1ConjugationIso A H g).inv ≫ h1Conjugation A H g = 𝟙 _ := by
  rw [h1Conjugation_eq_iso_hom]
  exact (h1ConjugationIso A H g).inv_hom_id

/-- Raw functorial composition compatibility for two conjugations. -/
theorem h1Conjugation_comp_raw
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (H : Subgroup G) (g h : G) :
    h1Conjugation A H g ≫
        h1Conjugation A (conjugateSubgroup H g) h =
      groupCohomology.map
        ((conjugateEquiv H g).symm.toMonoidHom.comp
          (conjugateEquiv
            (conjugateSubgroup H g) h).symm.toMonoidHom)
        (Rep.resMap
            (conjugateEquiv
              (conjugateSubgroup H g) h).symm.toMonoidHom
            (conjugationHom A H g) ≫
          conjugationHom A (conjugateSubgroup H g) h) 1 := by
  exact (groupCohomology.map_comp
    (conjugateEquiv H g).symm.toMonoidHom
    (conjugateEquiv
      (conjugateSubgroup H g) h).symm.toMonoidHom
    (conjugationHom A H g)
    (conjugationHom A (conjugateSubgroup H g) h) 1).symm

/-- Conjugation commutes with subgroup inclusion in the group variable. -/
theorem conjugate_inclusion_comm
    {G : Type u} [Group G] {K H : Subgroup G}
    (hKH : K ≤ H) (g : G) :
    (Subgroup.inclusion hKH).comp
        (conjugateEquiv K g).symm.toMonoidHom =
      (conjugateEquiv H g).symm.toMonoidHom.comp
        (Subgroup.inclusion (Subgroup.map_mono hKH)) := by
  ext x
  exact calc
    (((conjugateEquiv K g).symm x : K) : G) =
        g⁻¹ * (x : G) * g := coe_conjugateEquiv_symm K g x
    _ = g⁻¹ *
        ((Subgroup.inclusion (Subgroup.map_mono hKH) x :
          conjugateSubgroup H g) : G) * g := rfl
    _ = (((conjugateEquiv H g).symm
          (Subgroup.inclusion (Subgroup.map_mono hKH) x) : H) : G) :=
      (coe_conjugateEquiv_symm H g
        (Subgroup.inclusion (Subgroup.map_mono hKH) x)).symm


/-- Restriction commutes with conjugation, after using the canonical
nested/direct restriction comparisons on both sides. -/
theorem h1RestrictionBetween_conjugation
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) {K H : Subgroup G} (hKH : K ≤ H) (g : G) :
    h1RestrictionBetween A hKH ≫ h1Conjugation A K g =
      h1Conjugation A H g ≫
        h1RestrictionBetween A (conjugateSubgroup_mono hKH g) := by
  simp only [h1RestrictionBetween, h1Conjugation]
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · exact conjugate_inclusion_comm hKH g
  · ext x
    rfl

/-- The coefficient intertwiner for inner conjugation of the ambient group. -/
noncomputable def innerConjugationHom
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (g : G) :
    Rep.res (MulAut.conj g⁻¹).toMonoidHom A ⟶ A :=
  Rep.ofHom
    { toLinearMap := (actionLinearEquiv A g).toLinearMap
      isIntertwining' := by
        intro x
        ext v
        simp [actionLinearEquiv, mul_assoc] }

/-- The endomorphism of additive H¹ induced by inner conjugation and the
coefficient action. -/
noncomputable def h1InnerConjugation
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (g : G) :
    groupCohomology.H1 A ⟶ groupCohomology.H1 A :=
  groupCohomology.map (MulAut.conj g⁻¹).toMonoidHom
    (innerConjugationHom A g) 1

/-- Formula for inner conjugation on an additive one-cocycle. -/
theorem innerConjugation_mapCocycle_apply
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (g : G)
    (z : groupCohomology.cocycles₁ A) (x : G) :
    ((ConcreteCategory.hom
      (groupCohomology.mapCocycles₁
        (MulAut.conj g⁻¹).toMonoidHom
        (innerConjugationHom A g))) z : G → A) x =
      (A.ρ g) (z (g⁻¹ * x * g)) := by
  rw [groupCohomology.coe_mapCocycles₁]
  unfold groupCohomology.cochainsMap₁
  simp [innerConjugationHom, actionLinearEquiv]

/-- Inner conjugation changes an additive one-cocycle by the coboundary of
its value at the conjugating element. -/
theorem innerConjugation_mapCocycle_sub_apply
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (g : G)
    (z : groupCohomology.cocycles₁ A) (x : G) :
    ((ConcreteCategory.hom
      (groupCohomology.mapCocycles₁
        (MulAut.conj g⁻¹).toMonoidHom
        (innerConjugationHom A g))) z : G → A) x - z x =
      (A.ρ x) (z g) - z g := by
  have hz : ∀ a b : G, z (a * b) = (A.ρ a) (z b) + z a :=
    (groupCohomology.mem_cocycles₁_iff (A := A) z).mp z.property
  have hinv : (A.ρ g) (z g⁻¹) = -z g := by
    apply eq_neg_of_add_eq_zero_left
    have h := (hz g g⁻¹).symm
    simp only [mul_inv_cancel, groupCohomology.cocycles₁_map_one] at h
    exact h
  rw [innerConjugation_mapCocycle_apply]
  have hcancel :
      (A.ρ g) ((A.ρ g⁻¹) (z (x * g))) = z (x * g) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  calc
    (A.ρ g) (z (g⁻¹ * x * g)) - z x =
        (A.ρ g) (z (g⁻¹ * (x * g))) - z x := by
          rw [mul_assoc]
    _ = (A.ρ g) ((A.ρ g⁻¹) (z (x * g)) + z g⁻¹) - z x := by
          rw [hz]
    _ = (z (x * g) + (A.ρ g) (z g⁻¹)) - z x := by
          rw [map_add, hcancel]
    _ = (((A.ρ x) (z g) + z x) + (-z g)) - z x := by
          rw [hz, hinv]
    _ = (A.ρ x) (z g) - z g := by
          abel

/-- Inner conjugation acts trivially on additive first group cohomology. -/
@[simp]
theorem h1InnerConjugation_eq_id
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (g : G) :
    h1InnerConjugation A g = 𝟙 _ := by
  ext y
  have hsurjective :
      Function.Surjective
        (ConcreteCategory.hom (groupCohomology.H1π A)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, rfl⟩ := hsurjective y
  rw [h1InnerConjugation, groupCohomology.H1π_comp_map_apply]
  change
    ConcreteCategory.hom (groupCohomology.H1π A)
      ((ConcreteCategory.hom
        (groupCohomology.mapCocycles₁
          (MulAut.conj g⁻¹).toMonoidHom
          (innerConjugationHom A g))) z) =
    ConcreteCategory.hom (groupCohomology.H1π A) z
  let z' : groupCohomology.cocycles₁ A :=
    (ConcreteCategory.hom
      (groupCohomology.mapCocycles₁
        (MulAut.conj g⁻¹).toMonoidHom
        (innerConjugationHom A g))) z
  have hdiff :
      ((z' - z : groupCohomology.cocycles₁ A) : G → A) ∈
        groupCohomology.coboundaries₁ A := by
    refine ⟨z g, ?_⟩
    funext x
    rw [groupCohomology.d₀₁_hom_apply]
    change (A.ρ x) (z g) - z g = z' x - z x
    exact (innerConjugation_mapCocycle_sub_apply A g z x).symm
  have hzero :
      ConcreteCategory.hom (groupCohomology.H1π A) (z' - z) = 0 :=
    (groupCohomology.H1π_eq_zero_iff (z' - z)).2 hdiff
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero
end RiemannResearch.GroupCohomology
