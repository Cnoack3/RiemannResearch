/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.TwoGaugeDescent
import RiemannResearch.GroupCohomology.Conjugation

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

open RiemannResearch.GroupCohomology

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

/-- Every element transports the trivial subgroup to itself. Consequently the
bare `orientedSubgroupTransporter` predicate does not encode the maximal-torus
or E8 incidence needed by the intended application. -/
theorem mem_orientedSubgroupTransporter_bot
    {G : Type v} [Group G] (x : G) :
    x ∈ orientedSubgroupTransporter (⊥ : Subgroup G) (⊥ : Subgroup G)
      (MulEquiv.refl (↥(⊥ : Subgroup G))) := by
  intro s
  have hs : s = 1 := Subsingleton.elim _ _
  simp [hs]

/-- Two points of the same strict oriented transporter differ on the left by
an element centralizing the target subgroup. This is the torsor relation that
allows one fixed basepoint to control every oriented transition. -/
theorem leftQuotient_mem_centralizer_of_mem_orientedSubgroupTransporter
    {G : Type v} [Group G] (S6 S5 : Subgroup G) (theta : S6 ≃* S5)
    {x x0 : G}
    (hx : x ∈ orientedSubgroupTransporter S6 S5 theta)
    (hx0 : x0 ∈ orientedSubgroupTransporter S6 S5 theta) :
    x * x0⁻¹ ∈ Set.centralizer (S5 : Set G) := by
  rw [Set.mem_centralizer_iff]
  intro t ht
  let s : S6 := theta.symm ⟨t, ht⟩
  have hx' : x * s.1 * x⁻¹ = t := by
    simpa [s] using hx s
  have hx0' : x0 * s.1 * x0⁻¹ = t := by
    simpa [s] using hx0 s
  calc
    t * (x * x0⁻¹) =
        (x * s.1 * x⁻¹) * (x * x0⁻¹) := by rw [hx']
    _ = x * s.1 * x0⁻¹ := by simp [mul_assoc]
    _ = (x * x0⁻¹) * (x0 * s.1 * x0⁻¹) := by simp [mul_assoc]
    _ = (x * x0⁻¹) * t := by rw [hx0']

/-- Fixing one point identifies the strict oriented transporter with the
left coset of the target centralizer.

This is the point-valued torsor identity underlying the transporter reduction
in Beli--Gille--Lee, Proposition 2.5.3:
https://arxiv.org/pdf/1411.6808. The reference supports the geometric
interpretation; the proof here is elementary group algebra. -/
theorem mem_orientedSubgroupTransporter_iff_leftQuotient_mem_centralizer
    {G : Type v} [Group G] (S6 S5 : Subgroup G) (theta : S6 ≃* S5)
    {x x0 : G}
    (hx0 : x0 ∈ orientedSubgroupTransporter S6 S5 theta) :
    x ∈ orientedSubgroupTransporter S6 S5 theta ↔
      x * x0⁻¹ ∈ Set.centralizer (S5 : Set G) := by
  constructor
  · intro hx
    exact leftQuotient_mem_centralizer_of_mem_orientedSubgroupTransporter
      S6 S5 theta hx hx0
  · intro hc s
    have hcomm :
        (theta s).1 * (x * x0⁻¹) = (x * x0⁻¹) * (theta s).1 :=
      (Set.mem_centralizer_iff.mp hc) (theta s).1 (theta s).2
    calc
      x * s.1 * x⁻¹ =
          ((x * x0⁻¹) * x0) * s.1 * (((x * x0⁻¹) * x0)⁻¹) := by
            simp [mul_assoc]
      _ = (x * x0⁻¹) * (x0 * s.1 * x0⁻¹) * (x * x0⁻¹)⁻¹ := by
            simp [mul_assoc]
      _ = (x * x0⁻¹) * (theta s).1 * (x * x0⁻¹)⁻¹ := by
            rw [hx0 s]
      _ = (theta s).1 := by rw [← hcomm]; simp [mul_assoc]

/-- Conjugation by x0 supplies a canonical point of the strict oriented
transporter from S to its conjugate. The only arithmetic issue in applications
is whether the chosen conjugating element is fixed by the relevant Galois
subgroup. -/
theorem mem_orientedSubgroupTransporter_conjugateEquiv
    {G : Type v} [Group G] (S : Subgroup G) (x0 : G) :
    x0 ∈ orientedSubgroupTransporter S (conjugateSubgroup S x0)
      (conjugateEquiv S x0) := by
  intro s
  exact coe_conjugateEquiv S x0 s

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

/-- A factorization theorem only on the admissible oriented-transition locus
is sufficient for two-gauge descent.

This is the application-shaped endpoint for the binary-icosahedral E8
problem. It does not require the false ambient factorization of every element
of the overlap field group: only elements satisfying the overlap fixedness,
the matched-factorization crossing relations, and the supplied oriented-torus
incidence must factor through the two fixed-point groups. -/
theorem isCoboundary_of_admissible_orientedTransition_factorization
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (H K : Subgroup Γ) (hgen : H ⊔ K = ⊤)
    (gH gK : G)
    (hH : ∀ σ : H, a σ.1 = gH⁻¹ * σ.1 • gH)
    (hK : ∀ σ : K, a σ.1 = gK⁻¹ * σ.1 • gK)
    (S6 S5 : Subgroup G) (theta : S6 ≃* S5)
    (htransport :
      gH * gK⁻¹ ∈ orientedSubgroupTransporter S6 S5 theta)
    (hfactor :
      ∀ x : G,
        IsAdmissibleTwoGaugeTransition H K x →
        x ∈ orientedSubgroupTransporter S6 S5 theta →
        ∃ u v : G, NonabelianCocycle.IsFixedBy H u ∧
          NonabelianCocycle.IsFixedBy K v ∧ x = u * v) :
    a.IsCoboundary := by
  apply
    (isCoboundary_iff_transition_factorization
      a H K hgen gH gK hH hK).2
  exact hfactor (gH * gK⁻¹)
    (transition_isAdmissibleTwoGaugeTransition a H K gH gK hH hK)
    htransport

/-- A non-circular constrained factorization criterion for an oriented
transporter. If its target centralizer is H-fixed and it contains one K-fixed
basepoint, then every point of the transporter factors through the H- and
K-fixed point groups.

For the intended E8 application, the centralizer hypothesis is supplied by a
self-centralizing maximal torus defined over the H-field, while the basepoint
is a single oriented gauge representative defined over the K-field. -/
theorem orientedTransition_factorization_of_fixedBasepoint
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (H K : Subgroup Γ) (S6 S5 : Subgroup G) (theta : S6 ≃* S5)
    {x x0 : G}
    (hx : x ∈ orientedSubgroupTransporter S6 S5 theta)
    (hx0 : x0 ∈ orientedSubgroupTransporter S6 S5 theta)
    (hcentral :
      Set.centralizer (S5 : Set G) ⊆
        (fixedPointSubgroup (G := G) H : Set G))
    (hx0K : NonabelianCocycle.IsFixedBy K x0) :
    ∃ u v : G, NonabelianCocycle.IsFixedBy H u ∧
      NonabelianCocycle.IsFixedBy K v ∧ x = u * v := by
  have hquotientH : x * x0⁻¹ ∈ fixedPointSubgroup (G := G) H :=
    hcentral
      (leftQuotient_mem_centralizer_of_mem_orientedSubgroupTransporter
        S6 S5 theta hx hx0)
  refine ⟨x * x0⁻¹, x0, ?_, hx0K, ?_⟩
  · intro σ hσ
    exact hquotientH ⟨σ, hσ⟩
  · simp [mul_assoc]

/-- Exact two-gauge descent from two geometric incidence checks: one
K-fixed basepoint in the oriented transporter and H-fixedness of the target
centralizer.

Unlike the unrestricted transporter hypothesis, these assumptions exclude the
trivial-subgroup countermodel and isolate concrete E8 maximal-torus
obligations rather than assuming the desired factorization. -/
theorem isCoboundary_of_orientedTransition_fixedBasepoint
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (H K : Subgroup Γ) (hgen : H ⊔ K = ⊤)
    (gH gK : G)
    (hH : ∀ σ : H, a σ.1 = gH⁻¹ * σ.1 • gH)
    (hK : ∀ σ : K, a σ.1 = gK⁻¹ * σ.1 • gK)
    (S6 S5 : Subgroup G) (theta : S6 ≃* S5)
    (htransport :
      gH * gK⁻¹ ∈ orientedSubgroupTransporter S6 S5 theta)
    (x0 : G)
    (hx0 : x0 ∈ orientedSubgroupTransporter S6 S5 theta)
    (hcentral :
      Set.centralizer (S5 : Set G) ⊆
        (fixedPointSubgroup (G := G) H : Set G))
    (hx0K : NonabelianCocycle.IsFixedBy K x0) :
    a.IsCoboundary := by
  apply
    (isCoboundary_iff_transition_factorization
      a H K hgen gH gK hH hK).2
  exact orientedTransition_factorization_of_fixedBasepoint
    H K S6 S5 theta htransport hx0 hcentral hx0K

/-- Self-centralization of the target subgroup discharges the centralizer
hypothesis in constrained transporter factorization.

For a genuine maximal torus in a connected reductive group, the required
self-centralization is the standard theorem C_G(T) = T; see SGA 3, Expose XII:
https://webusers.imj-prg.fr/~patrick.polo/SGA3/Expo12.pdf. The reference
supports the E8 interpretation. This abstract declaration keeps both
self-centralization and pointwise H-fixedness explicit. -/
theorem orientedTransition_factorization_of_selfCentralizing_fixedBasepoint
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (H K : Subgroup Γ) (S6 S5 : Subgroup G) (theta : S6 ≃* S5)
    {x x0 : G}
    (hx : x ∈ orientedSubgroupTransporter S6 S5 theta)
    (hx0 : x0 ∈ orientedSubgroupTransporter S6 S5 theta)
    (hself : Set.centralizer (S5 : Set G) = (S5 : Set G))
    (hS5H : S5 ≤ fixedPointSubgroup (G := G) H)
    (hx0K : NonabelianCocycle.IsFixedBy K x0) :
    ∃ u v : G, NonabelianCocycle.IsFixedBy H u ∧
      NonabelianCocycle.IsFixedBy K v ∧ x = u * v := by
  apply orientedTransition_factorization_of_fixedBasepoint
    H K S6 S5 theta hx hx0
  · intro z hz
    apply hS5H
    simpa [hself] using hz
  · exact hx0K

/-- Conjugating one torus by a K-fixed element, together with target
self-centralization and pointwise H-fixedness, proves two-gauge neutrality.

This discharges all formal transporter and maximal-torus centralizer algebra.
It deliberately does not assert the existence of the K-fixed conjugating
element: in the EVIII application that is the rational-point problem for the
oriented torus torsor and remains the E8-specific arithmetic obligation. -/
theorem isCoboundary_of_selfCentralizing_conjugateTarget
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (H K : Subgroup Γ) (hgen : H ⊔ K = ⊤)
    (gH gK : G)
    (hH : ∀ σ : H, a σ.1 = gH⁻¹ * σ.1 • gH)
    (hK : ∀ σ : K, a σ.1 = gK⁻¹ * σ.1 • gK)
    (S6 : Subgroup G) (x0 : G)
    (htransport :
      gH * gK⁻¹ ∈
        orientedSubgroupTransporter S6 (conjugateSubgroup S6 x0)
          (conjugateEquiv S6 x0))
    (hself :
      Set.centralizer (conjugateSubgroup S6 x0 : Set G) =
        (conjugateSubgroup S6 x0 : Set G))
    (hS5H :
      conjugateSubgroup S6 x0 ≤ fixedPointSubgroup (G := G) H)
    (hx0K : NonabelianCocycle.IsFixedBy K x0) :
    a.IsCoboundary := by
  apply
    (isCoboundary_iff_transition_factorization
      a H K hgen gH gK hH hK).2
  exact orientedTransition_factorization_of_selfCentralizing_fixedBasepoint
    H K S6 (conjugateSubgroup S6 x0) (conjugateEquiv S6 x0)
      htransport (mem_orientedSubgroupTransporter_conjugateEquiv S6 x0)
      hself hS5H hx0K

/-- A kernel-checked no-go statement for replacing the missing E8 geometry by
the abstract transporter predicate alone.

If a locally trivial two-gauge cocycle is nonneutral, its transition is still
admissible and lies in an oriented transporter (take both subgroups trivial),
but it cannot factor through the two fixed-point groups. Thus any proof of the
E8 target must use a genuinely stronger compatibility notion: for example
maximal-torus incidence tied to the EVIII embedding or Allen-algebra data. -/
theorem abstract_orientedTransporter_does_not_strengthen_twoGaugeDescent
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G)
    (H K : Subgroup Γ) (hgen : H ⊔ K = ⊤)
    (gH gK : G)
    (hH : ∀ σ : H, a σ.1 = gH⁻¹ * σ.1 • gH)
    (hK : ∀ σ : K, a σ.1 = gK⁻¹ * σ.1 • gK)
    (hnontrivial : ¬ a.IsCoboundary) :
    IsAdmissibleTwoGaugeTransition H K (gH * gK⁻¹) ∧
      gH * gK⁻¹ ∈
        orientedSubgroupTransporter (⊥ : Subgroup G) (⊥ : Subgroup G)
          (MulEquiv.refl (↥(⊥ : Subgroup G))) ∧
      ¬ ∃ u v : G, NonabelianCocycle.IsFixedBy H u ∧
        NonabelianCocycle.IsFixedBy K v ∧ gH * gK⁻¹ = u * v := by
  refine ⟨transition_isAdmissibleTwoGaugeTransition a H K gH gK hH hK,
    mem_orientedSubgroupTransporter_bot (gH * gK⁻¹), ?_⟩
  intro hfactor
  exact hnontrivial
    ((isCoboundary_iff_transition_factorization
      a H K hgen gH gK hH hK).2 hfactor)

end RiemannResearch.GaloisCohomology
