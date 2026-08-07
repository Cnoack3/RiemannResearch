/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.GroupTheory.DoubleCoset
import RiemannResearch.GroupCohomology.Conjugation
import RiemannResearch.GroupCohomology.ArbitraryCorestriction

/-!
# Mackey double-coset geometry

This file formalizes the group-theoretic indexing and intersection equivalence
underlying the Mackey decomposition formula.  It deliberately does not assert
the cohomological sum formula: arbitrary finite-index corestriction on all
intersection subgroups is a separate construction.
-/

universe u

namespace RiemannResearch.GroupCohomology

/-- The double-coset set indexing restriction after corestriction from `H`
to `K`.  Our orientation is `K \\ G / H`. -/
abbrev MackeyDoubleCoset {G : Type u} [Group G]
    (H K : Subgroup G) :=
  DoubleCoset.Quotient (K : Set G) (H : Set G)

/-- A chosen representative of a Mackey double coset. -/
noncomputable def mackeyRepresentative
    {G : Type u} [Group G] (H K : Subgroup G)
    (q : MackeyDoubleCoset H K) : G :=
  Quotient.out q

@[simp]
theorem mackeyRepresentative_mk
    {G : Type u} [Group G] (H K : Subgroup G) (g : G) :
    DoubleCoset.mk K H
        (mackeyRepresentative H K (DoubleCoset.mk K H g)) =
      DoubleCoset.mk K H g := by
  exact DoubleCoset.out_eq' K H _

/-- Every group element is a left-`K`, right-`H` translate of the chosen
representative of its double coset. -/
theorem exists_mackey_decomposition
    {G : Type u} [Group G] (H K : Subgroup G) (g : G) :
    ∃ k : K, ∃ h : H,
      g = (k : G) * mackeyRepresentative H K
        (DoubleCoset.mk K H g) * (h : G) := by
  rcases DoubleCoset.mk_out_eq_mul K H g with
    ⟨k, h, hk, hh, hrep⟩
  refine ⟨⟨k⁻¹, K.inv_mem hk⟩, ⟨h⁻¹, H.inv_mem hh⟩, ?_⟩
  change g = k⁻¹ * Quotient.out (DoubleCoset.mk K H g) * h⁻¹
  rw [hrep]
  simp [mul_assoc]

/-- The source intersection `H ∩ g⁻¹Kg` in a Mackey summand. -/
def mackeySourceIntersection {G : Type u} [Group G]
    (H K : Subgroup G) (g : G) : Subgroup G :=
  H ⊓ conjugateSubgroup K g⁻¹

/-- The target intersection `K ∩ gHg⁻¹` in a Mackey summand. -/
def mackeyTargetIntersection {G : Type u} [Group G]
    (H K : Subgroup G) (g : G) : Subgroup G :=
  K ⊓ conjugateSubgroup H g

/-- Conjugation by `g` identifies the two intersection subgroups appearing
in the Mackey summand indexed by `KgH`. -/
noncomputable def mackeyIntersectionEquiv
    {G : Type u} [Group G] (H K : Subgroup G) (g : G) :
    mackeySourceIntersection H K g ≃*
      mackeyTargetIntersection H K g where
  toFun x := ⟨g * (x : G) * g⁻¹, by
    constructor
    · rcases x.property.2 with ⟨k, hk, hkx⟩
      change g * (x : G) * g⁻¹ ∈ K
      rw [← hkx]
      simpa [mul_assoc] using hk
    · exact ⟨(x : G), x.property.1, rfl⟩⟩
  invFun y := ⟨g⁻¹ * (y : G) * g, by
    constructor
    · rcases y.property.2 with ⟨h, hh, hhy⟩
      change g⁻¹ * (y : G) * g ∈ H
      rw [← hhy]
      simpa [mul_assoc] using hh
    · exact ⟨(y : G), y.property.1, by simp [mul_assoc]⟩⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv y := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_assoc]

@[simp]
theorem coe_mackeyIntersectionEquiv
    {G : Type u} [Group G] (H K : Subgroup G) (g : G)
    (x : mackeySourceIntersection H K g) :
    (mackeyIntersectionEquiv H K g x : G) =
      g * (x : G) * g⁻¹ := rfl

/-- A normal subgroup is unchanged by the project's explicit conjugate
subgroup construction. -/
theorem conjugateSubgroup_eq_self_of_normal
    {G : Type u} [Group G] (H : Subgroup G) [H.Normal] (g : G) :
    conjugateSubgroup H g = H := by
  apply le_antisymm
  · rintro x ⟨h, hh, rfl⟩
    exact (inferInstance : H.Normal).conj_mem h hh g
  · intro x hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · exact (inferInstance : H.Normal).conj_mem' x hx g
    · simp [mul_assoc]

theorem mackeySourceIntersection_eq_of_normal
    {G : Type u} [Group G] (H K : Subgroup G) [K.Normal] (g : G) :
    mackeySourceIntersection H K g = H ⊓ K := by
  rw [mackeySourceIntersection, conjugateSubgroup_eq_self_of_normal]

theorem mackeyTargetIntersection_eq_of_normal
    {G : Type u} [Group G] (H K : Subgroup G) [H.Normal] (g : G) :
    mackeyTargetIntersection H K g = K ⊓ H := by
  rw [mackeyTargetIntersection, conjugateSubgroup_eq_self_of_normal]

end RiemannResearch.GroupCohomology
