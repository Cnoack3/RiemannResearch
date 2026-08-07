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

end RiemannResearch.GroupCohomology
