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
transition factors. When every group element has a single H-K factorization,
the converse construction proves that overlap fixedness and the crossing
relations characterize exactly the transitions of normalized two-gauge
cocycles.
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

/-- Two gauges for the same restricted cocycle differ by a fixed element. -/
theorem transition_fixed_on_subgroup
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (S : Subgroup Γ) (g₁ g₂ : G)
    (h₁ : ∀ σ : S, a σ.1 = g₁⁻¹ * σ.1 • g₁)
    (h₂ : ∀ σ : S, a σ.1 = g₂⁻¹ * σ.1 • g₂) :
    NonabelianCocycle.IsFixedBy S (g₁ * g₂⁻¹) := by
  let H : Bool → Subgroup Γ := fun _ => S
  let gauges : Bool → G := fun i => if i then g₁ else g₂
  have hlocal : ∀ i, a.IsLocalGauge (H i) (gauges i) := by
    intro i σ hσ
    cases i <;> simp [H, gauges] at hσ ⊢
    · exact h₂ ⟨σ, hσ⟩
    · exact h₁ ⟨σ, hσ⟩
  have h := a.transition_fixed_on_inf H gauges hlocal true false
  simpa [H, gauges, NonabelianCocycle.transition] using h

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
      ∃ u v : G, NonabelianCocycle.IsFixedBy H u ∧
        NonabelianCocycle.IsFixedBy K v ∧
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

/-! ## Crossing relations for genuine two-gauge transitions

The transition between two local gauges is more constrained than an arbitrary
element fixed by their overlap. After gauging by the inverse of the
`K`-gauge, the cocycle is trivial on `K` and is the coboundary determined
by the transition on `H`. Comparing the two evaluations of a
refactorization `k * h = h' * k'` gives the crossing relation below.

In the binary-icosahedral application, `H` and `K` model the
binary-tetrahedral and binary-dihedral subgroups. Their product is the full
binary-icosahedral group and their overlap is cyclic of order four. Thus
these relations isolate the admissible transition locus on which the
E8-specific factorization theorem is actually needed.

Source: user-provided Serre-II E8 two-gauge program; the proof is elementary
nonabelian cocycle calculus.
-/

/-- The matched-factorization relations forced on a transition between local
gauges on two subgroups. -/
def SatisfiesTwoGaugeCrossingRelations
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (H K : Subgroup Γ) (δ : G) : Prop :=
  ∀ (k : K) (h h' : H) (k' : K),
    k.1 * h.1 = h'.1 * k'.1 →
      k.1 • (δ⁻¹ * h.1 • δ) = δ⁻¹ * h'.1 • δ

/-- A two-gauge transition is admissible when it is fixed on the overlap and
satisfies every crossing relation coming from a `K * H = H * K`
refactorization. -/
def IsAdmissibleTwoGaugeTransition
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (H K : Subgroup Γ) (δ : G) : Prop :=
  NonabelianCocycle.IsFixedBy (H ⊓ K) δ ∧
    SatisfiesTwoGaugeCrossingRelations H K δ

/-- Gauging by the inverse of the `K`-gauge normalizes the cocycle to one on
`K`; on `H` its values are the coboundary determined by the transition. -/
theorem normalizedTwoGauge_values
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (H K : Subgroup Γ) (gH gK : G)
    (hH : ∀ σ : H, a σ.1 = gH⁻¹ * σ.1 • gH)
    (hK : ∀ σ : K, a σ.1 = gK⁻¹ * σ.1 • gK) :
    let δ := gH * gK⁻¹
    let z := a.gauge gK⁻¹
    (∀ σ : K, z σ.1 = 1) ∧
      (∀ σ : H, z σ.1 = δ⁻¹ * σ.1 • δ) := by
  dsimp
  constructor
  · intro σ
    change (gK⁻¹)⁻¹ * a σ.1 * σ.1 • gK⁻¹ = 1
    rw [hK σ]
    have hinv : σ.1 • gK⁻¹ = (σ.1 • gK)⁻¹ :=
      map_inv (MulDistribMulAction.toMonoidHom G σ.1) gK
    rw [hinv]
    simp
  · intro σ
    change (gK⁻¹)⁻¹ * a σ.1 * σ.1 • gK⁻¹ =
      (gH * gK⁻¹)⁻¹ * σ.1 • (gH * gK⁻¹)
    rw [hH σ, smul_mul']
    simp [mul_assoc]

/-- After normalization, a value on a product `h * k` is determined entirely
by the transition and its `H` factor. -/
theorem normalizedTwoGauge_value_of_eq_mul
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (H K : Subgroup Γ) (gH gK : G)
    (hH : ∀ σ : H, a σ.1 = gH⁻¹ * σ.1 • gH)
    (hK : ∀ σ : K, a σ.1 = gK⁻¹ * σ.1 • gK)
    (γ : Γ) (h : H) (k : K) (hγ : γ = h.1 * k.1) :
    (a.gauge gK⁻¹) γ =
      (gH * gK⁻¹)⁻¹ * h.1 • (gH * gK⁻¹) := by
  let z := a.gauge gK⁻¹
  have hz := normalizedTwoGauge_values a H K gH gK hH hK
  calc
    z γ = z (h.1 * k.1) := by rw [hγ]
    _ = z h.1 * h.1 • z k.1 := z.map_mul' h.1 k.1
    _ = (gH * gK⁻¹)⁻¹ * h.1 • (gH * gK⁻¹) := by
      rw [hz.2 h, hz.1 k]
      simp only [MulDistribMulAction.smul_one, mul_one]

/-- Every genuine transition between two local gauges satisfies overlap
fixedness and all matched-factorization crossing relations. -/
theorem transition_isAdmissibleTwoGaugeTransition
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (H K : Subgroup Γ) (gH gK : G)
    (hH : ∀ σ : H, a σ.1 = gH⁻¹ * σ.1 • gH)
    (hK : ∀ σ : K, a σ.1 = gK⁻¹ * σ.1 • gK) :
    IsAdmissibleTwoGaugeTransition H K (gH * gK⁻¹) := by
  constructor
  · exact transition_fixed_on_subgroup a (H ⊓ K) gH gK
      (fun σ => hH ⟨σ.1, σ.2.1⟩)
      (fun σ => hK ⟨σ.1, σ.2.2⟩)
  · intro k h h' k' heq
    let z := a.gauge gK⁻¹
    have hz := normalizedTwoGauge_values a H K gH gK hH hK
    have hzK : ∀ σ : K, z σ.1 = 1 := hz.1
    have hzH :
        ∀ σ : H, z σ.1 =
          (gH * gK⁻¹)⁻¹ * σ.1 • (gH * gK⁻¹) := hz.2
    calc
      k.1 • ((gH * gK⁻¹)⁻¹ * h.1 • (gH * gK⁻¹)) =
          z k.1 * k.1 • z h.1 := by rw [hzK k, hzH h, one_mul]
      _ = z (k.1 * h.1) := (z.map_mul' k.1 h.1).symm
      _ = z (h'.1 * k'.1) := by rw [heq]
      _ = z h'.1 * h'.1 • z k'.1 := z.map_mul' h'.1 k'.1
      _ = (gH * gK⁻¹)⁻¹ * h'.1 • (gH * gK⁻¹) := by
        rw [hzH h', hzK k']
        simp only [MulDistribMulAction.smul_one, mul_one]

/-- Overlap fixedness makes the coboundary value attached to an H-factor
independent of an H-K decomposition.

The element comparing two H-factors lies simultaneously in H and K. -/
theorem overlap_fixed_value_eq_of_eq_mul
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (H K : Subgroup Γ) (δ : G)
    (hfixed : NonabelianCocycle.IsFixedBy (H ⊓ K) δ)
    (h h' : H) (k k' : K)
    (heq : h.1 * k.1 = h'.1 * k'.1) :
    δ⁻¹ * h.1 • δ = δ⁻¹ * h'.1 • δ := by
  let c : Γ := h'.1⁻¹ * h.1
  have hcH : c ∈ H := H.mul_mem (H.inv_mem h'.2) h.2
  have hc_eq : c = k'.1 * k.1⁻¹ := by
    dsimp [c]
    calc
      h'.1⁻¹ * h.1 =
          h'.1⁻¹ * (h.1 * k.1) * k.1⁻¹ := by simp [mul_assoc]
      _ = h'.1⁻¹ * (h'.1 * k'.1) * k.1⁻¹ := by rw [heq]
      _ = k'.1 * k.1⁻¹ := by simp
  have hcK : c ∈ K := by
    rw [hc_eq]
    exact K.mul_mem k'.2 (K.inv_mem k.2)
  have hcfix : c • δ = δ := hfixed c ⟨hcH, hcK⟩
  have hh : h.1 = h'.1 * c := by simp [c]
  rw [hh, mul_smul, hcfix]

/-- On a group with a single-product factorization Γ = H K, every admissible
transition is realized by a normalized nonabelian cocycle: the cocycle is
trivial on K and its restriction to H is the coboundary defined by δ.

The construction chooses one H-K decomposition for each group element.
Overlap fixedness makes its value independent of the chosen decomposition,
while the crossing relations are exactly what proves the cocycle identity. -/
theorem exists_normalizedTwoGaugeCocycle_of_isAdmissible
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (H K : Subgroup Γ)
    (hprod : ∀ γ : Γ, ∃ h : H, ∃ k : K, γ = h.1 * k.1)
    (δ : G) (hadm : IsAdmissibleTwoGaugeTransition H K δ) :
    ∃ a : NonabelianCocycle Γ G,
      (∀ k : K, a k.1 = 1) ∧
      (∀ h : H, a h.1 = δ⁻¹ * h.1 • δ) := by
  let left : Γ → H := fun γ => Classical.choose (hprod γ)
  let right : Γ → K := fun γ =>
    Classical.choose (Classical.choose_spec (hprod γ))
  have factor_spec : ∀ γ : Γ, γ = (left γ).1 * (right γ).1 := by
    intro γ
    exact Classical.choose_spec (Classical.choose_spec (hprod γ))
  let value : Γ → G := fun γ => δ⁻¹ * (left γ).1 • δ
  have value_eq_of_eq_mul :
      ∀ (γ : Γ) (h : H) (k : K), γ = h.1 * k.1 →
        value γ = δ⁻¹ * h.1 • δ := by
    intro γ h k hγ
    apply overlap_fixed_value_eq_of_eq_mul
      H K δ hadm.1 (left γ) h (right γ) k
    rw [← factor_spec γ, ← hγ]
  let a : NonabelianCocycle Γ G :=
    { toFun := value
      map_mul' := by
        intro γ₁ γ₂
        let h₁ : H := left γ₁
        let k₁ : K := right γ₁
        let h₂ : H := left γ₂
        let k₂ : K := right γ₂
        obtain ⟨h₃, k₃, hcross⟩ := hprod (k₁.1 * h₂.1)
        have hγ₁ : γ₁ = h₁.1 * k₁.1 := factor_spec γ₁
        have hγ₂ : γ₂ = h₂.1 * k₂.1 := factor_spec γ₂
        have hγmul :
            γ₁ * γ₂ = (h₁ * h₃).1 * (k₃ * k₂).1 := by
          rw [hγ₁, hγ₂]
          calc
            (h₁.1 * k₁.1) * (h₂.1 * k₂.1) =
                h₁.1 * (k₁.1 * h₂.1) * k₂.1 := by simp [mul_assoc]
            _ = h₁.1 * (h₃.1 * k₃.1) * k₂.1 := by rw [hcross]
            _ = (h₁ * h₃).1 * (k₃ * k₂).1 := by simp [mul_assoc]
        rw [value_eq_of_eq_mul γ₁ h₁ k₁ hγ₁,
          value_eq_of_eq_mul γ₂ h₂ k₂ hγ₂,
          value_eq_of_eq_mul
            (γ₁ * γ₂) (h₁ * h₃) (k₃ * k₂) hγmul,
          hγ₁, mul_smul, hadm.2 k₁ h₂ h₃ k₃ hcross]
        simp [smul_mul', mul_smul, mul_assoc] }
  refine ⟨a, ?_, ?_⟩
  · intro k
    have hk : k.1 = (1 : H).1 * k.1 := by simp
    change value k.1 = 1
    rw [value_eq_of_eq_mul k.1 1 k hk]
    simp
  · intro h
    have hh : h.1 = h.1 * (1 : K).1 := by simp
    change value h.1 = δ⁻¹ * h.1 • δ
    exact value_eq_of_eq_mul h.1 h 1 hh

/-- For Γ = H K, the admissibility relations characterize exactly the
transitions of normalized cocycles locally trivial on H and K. -/
theorem isAdmissibleTwoGaugeTransition_iff_exists_normalizedCocycle
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (H K : Subgroup Γ)
    (hprod : ∀ γ : Γ, ∃ h : H, ∃ k : K, γ = h.1 * k.1)
    (δ : G) :
    IsAdmissibleTwoGaugeTransition H K δ ↔
      ∃ a : NonabelianCocycle Γ G,
        (∀ k : K, a k.1 = 1) ∧
        (∀ h : H, a h.1 = δ⁻¹ * h.1 • δ) := by
  constructor
  · exact exists_normalizedTwoGaugeCocycle_of_isAdmissible H K hprod δ
  · rintro ⟨a, hK, hH⟩
    simpa using
      (transition_isAdmissibleTwoGaugeTransition a H K δ 1 hH
        (fun k => by
          simpa only [inv_one, one_mul, MulDistribMulAction.smul_one]
            using hK k))

end RiemannResearch.GaloisCohomology
