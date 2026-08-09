/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.LocalGaugeTransporter

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

/-- Backward-compatible two-gauge spelling of the general fixedness predicate. -/
abbrev FixedBy
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (S : Subgroup Γ) (g : G) : Prop :=
  NonabelianCocycle.IsFixedBy S g

/-- Two gauges for the same restricted cocycle differ by a fixed element. -/
theorem transition_fixed_on_subgroup
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (S : Subgroup Γ) (g₁ g₂ : G)
    (h₁ : ∀ σ : S, a σ.1 = g₁⁻¹ * σ.1 • g₁)
    (h₂ : ∀ σ : S, a σ.1 = g₂⁻¹ * σ.1 • g₂) :
    FixedBy S (g₁ * g₂⁻¹) := by
  let H : Bool → Subgroup Γ := fun _ => S
  let gauges : Bool → G := fun i => if i then g₁ else g₂
  have hlocal : ∀ i, a.IsLocalGauge (H i) (gauges i) := by
    intro i σ hσ
    cases i <;> simp [H, gauges] at hσ ⊢
    · exact h₂ ⟨σ, hσ⟩
    · exact h₁ ⟨σ, hσ⟩
  have h := a.transition_fixed_on_inf H gauges hlocal true false
  simpa [FixedBy, H, gauges, NonabelianCocycle.transition] using h

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
          _ = u⁻¹ := congrArg Inv.inv (hu σ.1 σ.2)
      rw [smul_mul', huInv]
      simp [mul_assoc]
    have hKg : ∀ σ : K, a σ.1 = g⁻¹ * σ.1 • g := by
      intro σ
      rw [hK σ, hgv]
      rw [smul_mul', hv σ.1 σ.2]
      simp
    exact a.isCoboundary_of_localGauges H K hgen g hHg hKg

end RiemannResearch.GaloisCohomology
