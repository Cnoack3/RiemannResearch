/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.TwoGaugeDescent

/-!
# Double-coset and oriented-transporter form of two-gauge descent

This module formalizes the abstract algebraic target in Proposition 6.15,
Proposition 6.19, and Research Target 8.1 of the E8 Serre II program.

For a finite Galois splitting field, the fixed-point subgroups below model
E8(L5) and E8(L6) inside E8(M). Global neutrality is equivalent to the
identity lying in the double coset of delta = g5 * g6⁻¹. The oriented
transporter theorem keeps the known incidence constraint visible.

It does not assert that the distinguished E8 double coset is trivial. That
existence statement is the E8-specific content still requested by Research
Target 8.1.
-/

namespace RiemannResearch.GaloisCohomology

universe u v

/-- Elements fixed pointwise by a subgroup form a subgroup. -/
def fixedPointSubgroup
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (S : Subgroup Γ) : Subgroup G where
  carrier := {x | ∀ σ : S, σ.1 • x = x}
  one_mem' := by
    intro σ
    exact (MulDistribMulAction.toMonoidHom G σ).map_one
  mul_mem' := by
    intro x y hx hy σ
    rw [smul_mul', hx σ, hy σ]
  inv_mem' := by
    intro x hx σ
    calc
      σ.1 • x⁻¹ = (σ.1 • x)⁻¹ :=
        map_inv (MulDistribMulAction.toMonoidHom G σ.1) x
      _ = x⁻¹ := congrArg Inv.inv (hx σ)

/-- The double coset A x B, written elementwise. -/
def subgroupDoubleCoset
    {G : Type v} [Group G] (A B : Subgroup G) (x : G) : Set G :=
  {y | ∃ a : A, ∃ b : B, y = a.1 * x * b.1}

/-- Product factorization is equivalent to triviality of the corresponding
double coset. -/
theorem factorization_iff_one_mem_subgroupDoubleCoset
    {G : Type v} [Group G] (A B : Subgroup G) (x : G) :
    (∃ a : A, ∃ b : B, x = a.1 * b.1) ↔
      1 ∈ subgroupDoubleCoset A B x := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a⁻¹, b⁻¹, by simp⟩
  · rintro ⟨a, b, h⟩
    refine ⟨a⁻¹, b⁻¹, ?_⟩
    calc
      x = a.1⁻¹ * (a.1 * x * b.1) * b.1⁻¹ := by simp [mul_assoc]
      _ = a.1⁻¹ * 1 * b.1⁻¹ := by rw [← h]
      _ = (a⁻¹ : A).1 * (b⁻¹ : B).1 := by simp

/-- The strict transporter whose points conjugate S6 to S5 with the specified
orientation. In the E8 application these subgroups are maximal tori over the
overlap field. -/
def orientedSubgroupTransporter
    {G : Type v} [Group G] (S6 S5 : Subgroup G) (theta : S6 ≃* S5) : Set G :=
  {x | ∀ s : S6, x * s.1 * x⁻¹ = (theta s).1}

@[simp] theorem mem_orientedSubgroupTransporter_iff
    {G : Type v} [Group G] (S6 S5 : Subgroup G) (theta : S6 ≃* S5) (x : G) :
    x ∈ orientedSubgroupTransporter S6 S5 theta ↔
      ∀ s : S6, x * s.1 * x⁻¹ = (theta s).1 := Iff.rfl

/-- Exact two-gauge descent expressed as a double-coset condition. -/
theorem isCoboundary_iff_one_mem_fixedPointDoubleCoset
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (H K : Subgroup Γ) (hgen : H ⊔ K = ⊤)
    (gH gK : G)
    (hH : ∀ σ : H, a σ.1 = gH⁻¹ * σ.1 • gH)
    (hK : ∀ σ : K, a σ.1 = gK⁻¹ * σ.1 • gK) :
    a.IsCoboundary ↔
      1 ∈ subgroupDoubleCoset
        (fixedPointSubgroup H) (fixedPointSubgroup K) (gH * gK⁻¹) := by
  rw [isCoboundary_iff_transition_factorization a H K hgen gH gK hH hK]
  constructor
  · rintro ⟨u, v, hu, hv, hdelta⟩
    apply (factorization_iff_one_mem_subgroupDoubleCoset
      (fixedPointSubgroup H) (fixedPointSubgroup K) (gH * gK⁻¹)).mp
    exact ⟨⟨u, fun σ => hu σ.1 σ.2⟩,
      ⟨v, fun σ => hv σ.1 σ.2⟩, hdelta⟩
  · intro h
    obtain ⟨u, v, hdelta⟩ :=
      (factorization_iff_one_mem_subgroupDoubleCoset
        (fixedPointSubgroup H) (fixedPointSubgroup K) (gH * gK⁻¹)).mpr h
    exact ⟨u.1, v.1, (fun σ hσ => u.2 ⟨σ, hσ⟩),
      (fun σ hσ => v.2 ⟨σ, hσ⟩), hdelta⟩

/-- If the transition lies in a prescribed oriented transporter, global
neutrality is equivalent to constrained double-coset triviality. The
transporter incidence is localization data, not a proof of factorization. -/
theorem isCoboundary_iff_orientedTransporter_and_doubleCoset
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (H K : Subgroup Γ) (hgen : H ⊔ K = ⊤)
    (gH gK : G)
    (hH : ∀ σ : H, a σ.1 = gH⁻¹ * σ.1 • gH)
    (hK : ∀ σ : K, a σ.1 = gK⁻¹ * σ.1 • gK)
    (S6 S5 : Subgroup G) (theta : S6 ≃* S5)
    (htransport :
      gH * gK⁻¹ ∈ orientedSubgroupTransporter S6 S5 theta) :
    a.IsCoboundary ↔
      (gH * gK⁻¹ ∈ orientedSubgroupTransporter S6 S5 theta ∧
        1 ∈ subgroupDoubleCoset
          (fixedPointSubgroup H) (fixedPointSubgroup K) (gH * gK⁻¹)) := by
  rw [isCoboundary_iff_one_mem_fixedPointDoubleCoset a H K hgen gH gK hH hK]
  exact ⟨fun h => ⟨htransport, h⟩, And.right⟩

end RiemannResearch.GaloisCohomology
