/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4DiscriminantForm

/-!
# D4-by-D4 discriminant graphs

Every D4 diagram symmetry is an isometry of the four-element discriminant
quadratic space. Its graph inside the discriminant group of `D4 ⊕ D4` is an
isotropic subgroup of order four, whose squared order is the order sixteen of
the ambient discriminant group.

This is the finite gluing datum used in the next integral-overlattice layer.
It is not, by itself, an E8 lattice, a D4-by-D4 subgroup of an algebraic
group, or a representation-theoretic triality construction.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

noncomputable section

theorem discriminantAction_zero (σ : DiagramSymmetry) :
    discriminantAction σ (0 : DiscriminantGroup) = 0 := by
  apply discriminantEquivParity.injective
  change
    discriminantEquivParity (discriminantActionPerm σ 0) =
      discriminantEquivParity 0
  rw [discriminantEquivParity_discriminantActionPerm_apply,
    discriminantEquivParity.map_zero]
  change modelActionFun σ 0 = 0
  revert σ
  decide

/-- The additive equivalence underlying one diagram symmetry on `P / Q`. -/
def discriminantActionAddEquiv
    (σ : DiagramSymmetry) :
    DiscriminantGroup ≃+ DiscriminantGroup where
  toEquiv := discriminantAction σ
  map_add' := discriminantAction_add σ

@[simp]
theorem discriminantActionAddEquiv_fundamentalClass
    (σ : DiagramSymmetry) (label : TrialityLabel) :
    discriminantActionAddEquiv σ (fundamentalClass label) =
      fundamentalClass (σ label) :=
  discriminantAction_fundamentalClass σ label

/-- The discriminant group of two orthogonal D4 copies. -/
abbrev PairDiscriminantGroup :=
  DiscriminantGroup × DiscriminantGroup

/-- The orthogonal-sum quadratic form on the pair discriminant group. -/
def pairDiscriminantQuadratic
    (x : PairDiscriminantGroup) : ZMod 2 :=
  discriminantQuadratic x.1 + discriminantQuadratic x.2

/-- The polarized pairing on the pair discriminant group. -/
def pairDiscriminantBilinear
    (x y : PairDiscriminantGroup) : ZMod 2 :=
  discriminantBilinear x.1 y.1 +
    discriminantBilinear x.2 y.2

/-- The additive graph map of a triality symmetry. -/
def discriminantGraphMap (τ : DiagramSymmetry) :
    DiscriminantGroup →+ PairDiscriminantGroup where
  toFun x := (x, discriminantAction τ x)
  map_zero' := by
    ext
    · rfl
    · exact discriminantAction_zero τ
  map_add' x y := by
    ext
    · rfl
    · exact discriminantAction_add τ x y

/-- The graph of a triality symmetry in the pair discriminant group. -/
def discriminantGraph (τ : DiagramSymmetry) :
    AddSubgroup PairDiscriminantGroup :=
  (discriminantGraphMap τ).range

@[simp]
theorem mem_discriminantGraph_iff
    (τ : DiagramSymmetry) (x : PairDiscriminantGroup) :
    x ∈ discriminantGraph τ ↔
      x.2 = discriminantAction τ x.1 := by
  constructor
  · rintro ⟨y, hy⟩
    have h1 := congrArg Prod.fst hy
    have h2 := congrArg Prod.snd hy
    change y = x.1 at h1
    change discriminantAction τ y = x.2 at h2
    rw [← h1]
    exact h2.symm
  · intro h
    refine ⟨x.1, ?_⟩
    apply Prod.ext
    · rfl
    · exact h.symm

/-- A triality graph is isotropic for the pair discriminant quadratic
form. -/
theorem discriminantGraph_isotropic
    (τ : DiagramSymmetry) {x : PairDiscriminantGroup}
    (hx : x ∈ discriminantGraph τ) :
    pairDiscriminantQuadratic x = 0 := by
  rw [mem_discriminantGraph_iff] at hx
  rw [pairDiscriminantQuadratic, hx,
    discriminantQuadratic_action]
  have hcharTwo : ∀ a : ZMod 2, a + a = 0 := by
    decide
  exact hcharTwo _

/-- The polarized pair form vanishes on every pair of elements of a triality
graph. -/
theorem discriminantGraph_totallyIsotropic
    (τ : DiagramSymmetry) {x y : PairDiscriminantGroup}
    (hx : x ∈ discriminantGraph τ)
    (hy : y ∈ discriminantGraph τ) :
    pairDiscriminantBilinear x y = 0 := by
  rw [mem_discriminantGraph_iff] at hx hy
  rw [pairDiscriminantBilinear, hx, hy,
    discriminantBilinear_action]
  have hcharTwo : ∀ a : ZMod 2, a + a = 0 := by
    decide
  exact hcharTwo _

theorem discriminantGraphMap_injective (τ : DiagramSymmetry) :
    Function.Injective (discriminantGraphMap τ) := by
  intro x y h
  exact congrArg Prod.fst h

/-- Projection to the first component identifies a triality graph with one
D4 discriminant group. -/
noncomputable def discriminantGroupEquivGraph
    (τ : DiagramSymmetry) :
    DiscriminantGroup ≃+ discriminantGraph τ :=
  AddEquiv.ofBijective (discriminantGraphMap τ).rangeRestrict
    ⟨by
      intro x y h
      apply discriminantGraphMap_injective τ
      exact congrArg Subtype.val h,
     AddMonoidHom.rangeRestrict_surjective _⟩

theorem natCard_discriminantGraph (τ : DiagramSymmetry) :
    Nat.card (discriminantGraph τ) = 4 := by
  rw [Nat.card_congr
    (discriminantGroupEquivGraph τ).toEquiv.symm]
  exact natCard_discriminantGroup

theorem natCard_pairDiscriminantGroup :
    Nat.card PairDiscriminantGroup = 16 := by
  simp only [Nat.card_prod]
  rw [natCard_discriminantGroup]

/-- The graph has square order equal to the order of the pair discriminant
group. This is the exact half-size calculation used by gluing. -/
theorem natCard_discriminantGraph_sq (τ : DiagramSymmetry) :
    Nat.card (discriminantGraph τ) ^ 2 =
      Nat.card PairDiscriminantGroup := by
  rw [natCard_discriminantGraph, natCard_pairDiscriminantGroup]
  norm_num

/-- Independent diagram actions on the two discriminant components. -/
def pairDiscriminantAction
    (σ₁ σ₂ : DiagramSymmetry) :
    Equiv.Perm PairDiscriminantGroup :=
  Equiv.prodCongr (discriminantAction σ₁)
    (discriminantAction σ₂)

theorem pairDiscriminantAction_add
    (σ₁ σ₂ : DiagramSymmetry) (x y : PairDiscriminantGroup) :
    pairDiscriminantAction σ₁ σ₂ (x + y) =
      pairDiscriminantAction σ₁ σ₂ x +
        pairDiscriminantAction σ₁ σ₂ y := by
  apply Prod.ext
  · exact discriminantAction_add σ₁ x.1 y.1
  · exact discriminantAction_add σ₂ x.2 y.2

/-- The pair action `(σ₁, σ₂)` preserves the graph of `τ` exactly when
`σ₂ τ = τ σ₁`. -/
theorem pairAction_preserves_discriminantGraph_iff
    (τ σ₁ σ₂ : DiagramSymmetry) :
    (∀ x, x ∈ discriminantGraph τ →
      pairDiscriminantAction σ₁ σ₂ x ∈ discriminantGraph τ) ↔
      σ₂ * τ = τ * σ₁ := by
  constructor
  · intro h
    apply discriminantAction_injective
    apply Equiv.ext
    intro x
    have hx :
        (x, discriminantAction τ x) ∈ discriminantGraph τ := by
      rw [mem_discriminantGraph_iff]
    have himage := h _ hx
    rw [mem_discriminantGraph_iff] at himage
    change
      discriminantAction σ₂ (discriminantAction τ x) =
        discriminantAction τ (discriminantAction σ₁ x) at himage
    have hleft :=
      DFunLike.congr_fun (discriminantAction.map_mul σ₂ τ) x
    change
      discriminantAction (σ₂ * τ) x =
        discriminantAction σ₂ (discriminantAction τ x) at hleft
    have hright :=
      DFunLike.congr_fun (discriminantAction.map_mul τ σ₁) x
    change
      discriminantAction (τ * σ₁) x =
        discriminantAction τ (discriminantAction σ₁ x) at hright
    exact hleft.trans (himage.trans hright.symm)
  · intro h x hx
    rw [mem_discriminantGraph_iff] at hx ⊢
    change
      discriminantAction σ₂ x.2 =
        discriminantAction τ (discriminantAction σ₁ x.1)
    rw [hx]
    have hperm := congrArg discriminantAction h
    have heval := DFunLike.congr_fun hperm x.1
    have hleft :=
      DFunLike.congr_fun (discriminantAction.map_mul σ₂ τ) x.1
    change
      discriminantAction (σ₂ * τ) x.1 =
        discriminantAction σ₂
          (discriminantAction τ x.1) at hleft
    have hright :=
      DFunLike.congr_fun (discriminantAction.map_mul τ σ₁) x.1
    change
      discriminantAction (τ * σ₁) x.1 =
        discriminantAction τ
          (discriminantAction σ₁ x.1) at hright
    exact hleft.symm.trans (heval.trans hright)

/-- A pair of D4 triality actions preserves the identity gluing graph exactly
when the two actions are synchronized.

This is the finite discriminant-form meaning of synchronized D4-by-D4
triality: independent outer actions do not extend across the diagonal glue
unless they agree. -/
theorem pairAction_preserves_identityGraph_iff_synchronized
    (σ₁ σ₂ : DiagramSymmetry) :
    (∀ x, x ∈ discriminantGraph 1 →
      pairDiscriminantAction σ₁ σ₂ x ∈ discriminantGraph 1) ↔
      σ₂ = σ₁ := by
  rw [pairAction_preserves_discriminantGraph_iff]
  simp

/-- The diagonal S3 action preserves the identity gluing graph. -/
theorem diagonalPairAction_preserves_identityGraph
    (σ : DiagramSymmetry) :
    ∀ x, x ∈ discriminantGraph 1 →
      pairDiscriminantAction σ σ x ∈ discriminantGraph 1 := by
  rw [pairAction_preserves_discriminantGraph_iff]
  simp

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
