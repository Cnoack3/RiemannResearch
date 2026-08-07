/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.NonabelianH1

/-!
# Two-gauge nonabelian descent

This module isolates the exact algebraic content of the binary-icosahedral
two-field argument. A cocycle trivialized on two generating subgroups is
globally trivial exactly when the transition between the two local gauges
factors as a product of elements fixed by the respective subgroups.

For a finite Galois splitting field, the two fixed subgroups model the groups
of rational points over the two intermediate fields. The final theorem is the
abstract double-coset factorization criterion; it does not assert that every
transition factors.
-/

namespace RiemannResearch.GaloisCohomology

universe u v

/-- Every nonabelian one-cocycle takes the identity to the identity. -/
theorem NonabelianCocycle.map_one
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G) :
    a 1 = 1 := by
  have h := a.map_mul' 1 1
  have h' : a 1 * 1 = a 1 * a 1 := by simpa using h
  exact (mul_left_cancel h').symm

/-- The subgroup on which a nonabelian cocycle is pointwise trivial. -/
def NonabelianCocycle.trivialitySubgroup
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G) :
    Subgroup Γ where
  carrier := {σ | a σ = 1}
  one_mem' := a.map_one
  mul_mem' := by
    intro σ τ hσ hτ
    change a (σ * τ) = 1
    change a σ = 1 at hσ
    change a τ = 1 at hτ
    rw [a.map_mul', hσ, hτ]
    have hσ1 : σ • (1 : G) = 1 :=
      (MulDistribMulAction.toMonoidHom G σ).map_one
    rw [hσ1, mul_one]
  inv_mem' := by
    intro σ hσ
    change a σ⁻¹ = 1
    change a σ = 1 at hσ
    have h := a.map_mul' σ⁻¹ σ
    have hσ1 : σ⁻¹ • (1 : G) = 1 :=
      (MulDistribMulAction.toMonoidHom G σ⁻¹).map_one
    rw [inv_mul_cancel σ, a.map_one, hσ, hσ1, mul_one] at h
    exact h.symm

/-- A cocycle which is one on each of two generating subgroups is trivial. -/
theorem NonabelianCocycle.eq_trivial_of_eq_one_on_generators
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (H K : Subgroup Γ) (hgen : H ⊔ K = ⊤)
    (hH : ∀ σ : H, a σ.1 = 1)
    (hK : ∀ σ : K, a σ.1 = 1) :
    a = NonabelianCocycle.trivial := by
  have hHle : H ≤ a.trivialitySubgroup := by
    intro σ hσ
    change a σ = 1
    exact hH ⟨σ, hσ⟩
  have hKle : K ≤ a.trivialitySubgroup := by
    intro σ hσ
    change a σ = 1
    exact hK ⟨σ, hσ⟩
  have htop : (⊤ : Subgroup Γ) ≤ a.trivialitySubgroup := by
    rw [← hgen]
    exact sup_le hHle hKle
  ext σ
  have hσ := htop (Subgroup.mem_top σ)
  change a σ = 1 at hσ
  exact hσ

/-- Compatible local gauge formulas on two generating subgroups give a global
coboundary. -/
theorem NonabelianCocycle.isCoboundary_of_localGauges
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (H K : Subgroup Γ) (hgen : H ⊔ K = ⊤) (g : G)
    (hH : ∀ σ : H, a σ.1 = g⁻¹ * σ.1 • g)
    (hK : ∀ σ : K, a σ.1 = g⁻¹ * σ.1 • g) :
    a.IsCoboundary := by
  let z := a.gauge g⁻¹
  have hzH : ∀ σ : H, z σ.1 = 1 := by
    intro σ
    change (g⁻¹)⁻¹ * a σ.1 * σ.1 • g⁻¹ = 1
    rw [hH σ]
    have hinv : σ.1 • g⁻¹ = (σ.1 • g)⁻¹ :=
      map_inv (MulDistribMulAction.toMonoidHom G σ.1) g
    rw [hinv]
    simp
  have hzK : ∀ σ : K, z σ.1 = 1 := by
    intro σ
    change (g⁻¹)⁻¹ * a σ.1 * σ.1 • g⁻¹ = 1
    rw [hK σ]
    have hinv : σ.1 • g⁻¹ = (σ.1 • g)⁻¹ :=
      map_inv (MulDistribMulAction.toMonoidHom G σ.1) g
    rw [hinv]
    simp
  have hz : z = NonabelianCocycle.trivial :=
    z.eq_trivial_of_eq_one_on_generators H K hgen hzH hzK
  refine ⟨g, ?_⟩
  have hgauged := congrArg (fun b : NonabelianCocycle Γ G => b.gauge g) hz
  simpa [z, NonabelianCocycle.gauge_gauge,
    NonabelianCocycle.gauge_one] using hgauged

/-- An element fixed by the action of a subgroup. -/
def FixedBy
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (S : Subgroup Γ) (g : G) : Prop :=
  ∀ σ : S, σ.1 • g = g

/-- Two gauges for the same restricted cocycle differ by a fixed element. -/
theorem transition_fixed_on_subgroup
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (S : Subgroup Γ) (g₁ g₂ : G)
    (h₁ : ∀ σ : S, a σ.1 = g₁⁻¹ * σ.1 • g₁)
    (h₂ : ∀ σ : S, a σ.1 = g₂⁻¹ * σ.1 • g₂) :
    FixedBy S (g₁ * g₂⁻¹) := by
  intro σ
  have e₁ : σ.1 • g₁ = g₁ * a σ.1 := by
    rw [h₁ σ]
    simp
  have e₂ : σ.1 • g₂ = g₂ * a σ.1 := by
    rw [h₂ σ]
    simp
  rw [smul_mul']
  have hinv : σ.1 • g₂⁻¹ = (σ.1 • g₂)⁻¹ :=
    map_inv (MulDistribMulAction.toMonoidHom G σ.1) g₂
  rw [hinv, e₁, e₂]
  simp [mul_assoc]

/-- Exact two-gauge descent: global neutrality is equivalent to factorization
of the transition by the two fixed subgroups. -/
theorem isCoboundary_iff_transition_factorization
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (H K : Subgroup Γ) (hgen : H ⊔ K = ⊤)
    (gH gK : G)
    (hH : ∀ σ : H, a σ.1 = gH⁻¹ * σ.1 • gH)
    (hK : ∀ σ : K, a σ.1 = gK⁻¹ * σ.1 • gK) :
    a.IsCoboundary ↔
      ∃ u v : G, FixedBy H u ∧ FixedBy K v ∧
        gH * gK⁻¹ = u * v := by
  constructor
  · rintro ⟨g, hg⟩
    have hglobal : ∀ σ : Γ, a σ = g⁻¹ * σ • g := by
      intro σ
      rw [hg]
      simp [NonabelianCocycle.gauge, NonabelianCocycle.trivial]
    refine ⟨gH * g⁻¹, g * gK⁻¹, ?_, ?_, ?_⟩
    · exact transition_fixed_on_subgroup a H gH g hH
        (fun σ => hglobal σ.1)
    · exact transition_fixed_on_subgroup a K g gK
        (fun σ => hglobal σ.1) hK
    · simp [mul_assoc]
  · rintro ⟨u, v, hu, hv, hfac⟩
    let g : G := u⁻¹ * gH
    have hgv : g = v * gK := by
      change u⁻¹ * gH = v * gK
      calc
        u⁻¹ * gH = u⁻¹ * (gH * gK⁻¹) * gK := by
          simp [mul_assoc]
        _ = u⁻¹ * (u * v) * gK := by rw [hfac]
        _ = v * gK := by simp
    have hHg : ∀ σ : H, a σ.1 = g⁻¹ * σ.1 • g := by
      intro σ
      rw [hH σ]
      change gH⁻¹ * σ.1 • gH =
        (u⁻¹ * gH)⁻¹ * σ.1 • (u⁻¹ * gH)
      have huInv : σ.1 • u⁻¹ = u⁻¹ := by
        calc
          σ.1 • u⁻¹ = (σ.1 • u)⁻¹ :=
            map_inv (MulDistribMulAction.toMonoidHom G σ.1) u
          _ = u⁻¹ := congrArg Inv.inv (hu σ)
      rw [smul_mul', huInv]
      simp [mul_assoc]
    have hKg : ∀ σ : K, a σ.1 = g⁻¹ * σ.1 • g := by
      intro σ
      rw [hK σ, hgv]
      rw [smul_mul', hv σ]
      simp
    exact a.isCoboundary_of_localGauges H K hgen g hHg hKg

end RiemannResearch.GaloisCohomology
