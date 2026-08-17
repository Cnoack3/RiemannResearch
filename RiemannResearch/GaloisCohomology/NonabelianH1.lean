/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Actions

/-!
# Nonabelian first cohomology

This module defines the pointed set of nonabelian one-cocycles for a discrete
group acting by automorphisms on a group. It supplies gauge equivalence,
neutrality, coboundaries, and restriction to a subgroup.

This is the finite-group foundation needed to replace abstract neutrality and
restriction predicates in the E8 descent modules. It does not yet model
continuity for a profinite absolute Galois group, algebraic group schemes, or
the identification of torsors with nonabelian Galois cohomology.
-/

universe u v w

namespace RiemannResearch.GaloisCohomology

/-- A nonabelian one-cocycle for an action of `Γ` on `G` by group
automorphisms. The convention is
`a (σ * τ) = a σ * σ • a τ`. -/
structure NonabelianCocycle
    (Γ : Type u) (G : Type v) [Group Γ] [Group G]
    [MulDistribMulAction Γ G] where
  /-- The underlying inhomogeneous one-cochain. -/
  toFun : Γ → G
  /-- The nonabelian cocycle identity. -/
  map_mul' : ∀ σ τ, toFun (σ * τ) = toFun σ * σ • toFun τ

instance {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] :
    CoeFun (NonabelianCocycle Γ G) (fun _ => Γ → G) :=
  ⟨NonabelianCocycle.toFun⟩

/-- Two nonabelian cocycles are equal when their cochains agree pointwise. -/
@[ext]
theorem NonabelianCocycle.ext
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] {a b : NonabelianCocycle Γ G}
    (h : ∀ σ, a σ = b σ) : a = b := by
  cases a with
  | mk af ah =>
    cases b with
    | mk bf bh =>
      have hab : af = bf := funext h
      subst bf
      rfl

/-- The trivial nonabelian cocycle. -/
def NonabelianCocycle.trivial
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] : NonabelianCocycle Γ G where
  toFun := fun _ => 1
  map_mul' := by
    intro σ τ
    simp only [one_mul]
    exact (MulDistribMulAction.toMonoidHom G σ).map_one.symm

/-- Gauge a cocycle by `g`. This convention sends `a σ` to
`g⁻¹ * a σ * σ • g`. -/
def NonabelianCocycle.gauge
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (g : G) (a : NonabelianCocycle Γ G) :
    NonabelianCocycle Γ G where
  toFun := fun σ => g⁻¹ * a σ * σ • g
  map_mul' := by
    intro σ τ
    rw [a.map_mul']
    have hσinv : σ • g⁻¹ = (σ • g)⁻¹ :=
      map_inv (MulDistribMulAction.toMonoidHom G σ) g
    simp [smul_mul', hσinv, mul_smul, mul_assoc]

/-- Gauging by the identity does nothing. -/
theorem NonabelianCocycle.gauge_one
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G) :
    a.gauge 1 = a := by
  ext σ
  simp only [gauge, inv_one, one_mul, MulDistribMulAction.smul_one, mul_one]

/-- Successive gauges multiply in the order dictated by the right gauge
action. -/
theorem NonabelianCocycle.gauge_gauge
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (g h : G) (a : NonabelianCocycle Γ G) :
    (a.gauge h).gauge g = a.gauge (h * g) := by
  ext σ
  simp [gauge, smul_mul', mul_assoc]

/-- Gauge equivalence of nonabelian cocycles. -/
def NonabelianCocycle.Cohomologous
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (a b : NonabelianCocycle Γ G) : Prop :=
  ∃ g : G, b = a.gauge g

/-- Gauge equivalence is reflexive. -/
theorem NonabelianCocycle.cohomologous_refl
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G) :
    a.Cohomologous a := by
  refine ⟨1, ?_⟩
  exact a.gauge_one.symm

/-- Gauge equivalence is symmetric. -/
theorem NonabelianCocycle.cohomologous_symm
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] {a b : NonabelianCocycle Γ G} :
    a.Cohomologous b → b.Cohomologous a := by
  rintro ⟨g, rfl⟩
  refine ⟨g⁻¹, ?_⟩
  rw [gauge_gauge]
  simpa using a.gauge_one.symm

/-- Gauge equivalence is transitive. -/
theorem NonabelianCocycle.cohomologous_trans
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] {a b c : NonabelianCocycle Γ G} :
    a.Cohomologous b → b.Cohomologous c → a.Cohomologous c := by
  rintro ⟨g, rfl⟩ ⟨h, rfl⟩
  refine ⟨g * h, ?_⟩
  exact gauge_gauge h g a

/-- The setoid of nonabelian cocycles modulo gauge equivalence. -/
def NonabelianCocycle.setoid
    (Γ : Type u) (G : Type v) [Group Γ] [Group G]
    [MulDistribMulAction Γ G] : Setoid (NonabelianCocycle Γ G) where
  r := NonabelianCocycle.Cohomologous
  iseqv := ⟨NonabelianCocycle.cohomologous_refl,
    NonabelianCocycle.cohomologous_symm,
    NonabelianCocycle.cohomologous_trans⟩

instance NonabelianCocycle.instSetoid
    (Γ : Type u) (G : Type v) [Group Γ] [Group G]
    [MulDistribMulAction Γ G] : Setoid (NonabelianCocycle Γ G) :=
  NonabelianCocycle.setoid Γ G

/-- A cocycle is a coboundary when it is a gauge of the trivial cocycle. -/
def NonabelianCocycle.IsCoboundary
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G) : Prop :=
  ∃ g : G, a = (trivial : NonabelianCocycle Γ G).gauge g

/-- A cocycle is cohomologous to the trivial cocycle exactly when it is a
coboundary. -/
theorem NonabelianCocycle.cohomologous_trivial_iff_isCoboundary
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G) :
    a.Cohomologous trivial ↔ a.IsCoboundary := by
  constructor
  · intro h
    have hs := NonabelianCocycle.cohomologous_symm h
    simpa [IsCoboundary, Cohomologous] using hs
  · intro h
    have hs :
        (trivial : NonabelianCocycle Γ G).Cohomologous a := by
      simpa [IsCoboundary, Cohomologous] using h
    exact NonabelianCocycle.cohomologous_symm hs

/-- Restriction of a nonabelian cocycle to a subgroup. -/
def NonabelianCocycle.restrict
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (S : Subgroup Γ)
    (a : NonabelianCocycle Γ G) : NonabelianCocycle S G where
  toFun := fun σ => a σ.1
  map_mul' := by
    intro σ τ
    exact a.map_mul' σ.1 τ.1

/-- Restriction preserves the trivial cocycle. -/
@[simp]
theorem NonabelianCocycle.restrict_trivial
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (S : Subgroup Γ) :
    (trivial : NonabelianCocycle Γ G).restrict S =
      (trivial : NonabelianCocycle S G) := by
  ext σ
  rfl

/-- Restriction commutes with a gauge transformation. -/
theorem NonabelianCocycle.restrict_gauge
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (S : Subgroup Γ)
    (g : G) (a : NonabelianCocycle Γ G) :
    (a.gauge g).restrict S = (a.restrict S).gauge g := by
  ext σ
  rfl

/-- Nonabelian first cohomology as a pointed quotient set. -/
def NonabelianH1
    (Γ : Type u) (G : Type v) [Group Γ] [Group G]
    [MulDistribMulAction Γ G] :=
  Quotient (NonabelianCocycle.setoid Γ G)

namespace NonabelianH1

/-- The class of a nonabelian cocycle. -/
def classOf
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (a : NonabelianCocycle Γ G) : NonabelianH1 Γ G :=
  Quotient.mk' a

/-- The distinguished neutral element of nonabelian first cohomology. -/
def neutral
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] : NonabelianH1 Γ G :=
  classOf NonabelianCocycle.trivial

/-- The neutral class is the distinguished point of nonabelian first
cohomology. -/
instance instOne
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] : One (NonabelianH1 Γ G) :=
  ⟨neutral⟩

/-- Equality of cohomology classes is gauge equivalence. -/
theorem classOf_eq_classOf_iff
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a b : NonabelianCocycle Γ G) :
    classOf a = classOf b ↔ a.Cohomologous b :=
  Quotient.eq_iff_equiv

/-- A cocycle represents the neutral class exactly when it is a coboundary. -/
theorem classOf_eq_neutral_iff_isCoboundary
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (a : NonabelianCocycle Γ G) :
    classOf a = neutral ↔ a.IsCoboundary := by
  rw [neutral, classOf_eq_classOf_iff,
    NonabelianCocycle.cohomologous_trivial_iff_isCoboundary]

/-- Restriction on nonabelian first cohomology. -/
def restrict
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (S : Subgroup Γ) :
    NonabelianH1 Γ G → NonabelianH1 S G :=
  Quotient.map (NonabelianCocycle.restrict S) (by
    intro a b hab
    rcases hab with ⟨g, rfl⟩
    exact ⟨g, (NonabelianCocycle.restrict_gauge S g a).symm⟩)

/-- Restriction applied to a represented class. -/
@[simp]
theorem restrict_classOf
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (S : Subgroup Γ)
    (a : NonabelianCocycle Γ G) :
    restrict S (classOf a) = classOf (a.restrict S) :=
  rfl

/-- Restriction sends the neutral class to the neutral class. -/
@[simp]
theorem restrict_neutral
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (S : Subgroup Γ) :
    restrict S (neutral : NonabelianH1 Γ G) =
      (neutral : NonabelianH1 S G) := by
  rw [neutral, restrict_classOf, NonabelianCocycle.restrict_trivial]
  rfl

/-- Restriction to the trivial subgroup is always neutral.

This is the terminal step used when a cohomology class is restricted along a
finite Galois tower all the way to its common splitting field. -/
theorem restrict_bot_eq_neutral
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G]
    (z : NonabelianH1 Γ G) :
    restrict (⊥ : Subgroup Γ) z =
      (neutral : NonabelianH1 (⊥ : Subgroup Γ) G) := by
  refine Quotient.inductionOn z (fun a => ?_)
  change restrict (⊥ : Subgroup Γ) (classOf a) = neutral
  rw [restrict_classOf, classOf_eq_neutral_iff_isCoboundary]
  refine ⟨1, ?_⟩
  ext σ
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst σ
  simp only [NonabelianCocycle.restrict, NonabelianCocycle.gauge,
    NonabelianCocycle.trivial, inv_one, MulDistribMulAction.smul_one, mul_one]
  have h := a.map_mul' 1 1
  simp only [one_mul, one_smul] at h
  calc
    a 1 = (a 1)⁻¹ * (a 1 * a 1) := by simp
    _ = (a 1)⁻¹ * a 1 := by rw [← h]
    _ = 1 := by simp

/-- The proposition that a nonabelian first-cohomology class is neutral. -/
def IsNeutral
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (x : NonabelianH1 Γ G) : Prop :=
  x = neutral

/-- Restriction preserves neutrality, with no citation or additional
hypothesis. -/
theorem restrict_preserves_neutrality
    {Γ : Type u} {G : Type v} [Group Γ] [Group G]
    [MulDistribMulAction Γ G] (S : Subgroup Γ)
    {x : NonabelianH1 Γ G} (hx : IsNeutral x) :
    IsNeutral (restrict S x) := by
  rw [IsNeutral] at hx ⊢
  rw [hx, restrict_neutral]

end NonabelianH1

/-- Push a nonabelian cocycle forward along an equivariant group
homomorphism. -/
def NonabelianCocycle.map
    {Γ : Type u} {G : Type v} {H : Type w}
    [Group Γ] [Group G] [Group H]
    [MulDistribMulAction Γ G] [MulDistribMulAction Γ H]
    (φ : G →* H) (hφ : ∀ (σ : Γ) (g : G), φ (σ • g) = σ • φ g)
    (a : NonabelianCocycle Γ G) : NonabelianCocycle Γ H where
  toFun := fun σ => φ (a σ)
  map_mul' := by
    intro σ τ
    rw [a.map_mul', map_mul, hφ]

/-- Pushing forward commutes with a gauge transformation. -/
theorem NonabelianCocycle.map_gauge
    {Γ : Type u} {G : Type v} {H : Type w}
    [Group Γ] [Group G] [Group H]
    [MulDistribMulAction Γ G] [MulDistribMulAction Γ H]
    (φ : G →* H) (hφ : ∀ (σ : Γ) (g : G), φ (σ • g) = σ • φ g)
    (g : G) (a : NonabelianCocycle Γ G) :
    (a.gauge g).map φ hφ = (a.map φ hφ).gauge (φ g) := by
  ext σ
  simp [map, gauge, hφ]

namespace NonabelianH1

/-- Pushforward on nonabelian first cohomology along an equivariant group
homomorphism. -/
def map
    {Γ : Type u} {G : Type v} {H : Type w}
    [Group Γ] [Group G] [Group H]
    [MulDistribMulAction Γ G] [MulDistribMulAction Γ H]
    (φ : G →* H) (hφ : ∀ (σ : Γ) (g : G), φ (σ • g) = σ • φ g) :
    NonabelianH1 Γ G → NonabelianH1 Γ H :=
  Quotient.map (NonabelianCocycle.map φ hφ) (by
    intro a b hab
    rcases hab with ⟨g, rfl⟩
    exact ⟨φ g, NonabelianCocycle.map_gauge φ hφ g a⟩)

/-- Pushforward applied to a represented class. -/
@[simp]
theorem map_classOf
    {Γ : Type u} {G : Type v} {H : Type w}
    [Group Γ] [Group G] [Group H]
    [MulDistribMulAction Γ G] [MulDistribMulAction Γ H]
    (φ : G →* H) (hφ : ∀ (σ : Γ) (g : G), φ (σ • g) = σ • φ g)
    (a : NonabelianCocycle Γ G) :
    map φ hφ (classOf a) = classOf (a.map φ hφ) :=
  rfl

/-- Pushforward sends the neutral class to the neutral class. -/
@[simp]
theorem map_neutral
    {Γ : Type u} {G : Type v} {H : Type w}
    [Group Γ] [Group G] [Group H]
    [MulDistribMulAction Γ G] [MulDistribMulAction Γ H]
    (φ : G →* H) (hφ : ∀ (σ : Γ) (g : G), φ (σ • g) = σ • φ g) :
    map φ hφ (neutral : NonabelianH1 Γ G) =
      (neutral : NonabelianH1 Γ H) := by
  rw [neutral, map_classOf]
  apply congrArg classOf
  ext σ
  simp [NonabelianCocycle.map, NonabelianCocycle.trivial]

/-- An equivariant group homomorphism sends a neutral nonabelian cohomology
class to a neutral class. -/
theorem map_preserves_neutrality
    {Γ : Type u} {G : Type v} {H : Type w}
    [Group Γ] [Group G] [Group H]
    [MulDistribMulAction Γ G] [MulDistribMulAction Γ H]
    (φ : G →* H) (hφ : ∀ (σ : Γ) (g : G), φ (σ • g) = σ • φ g)
    {x : NonabelianH1 Γ G} (hx : IsNeutral x) :
    IsNeutral (map φ hφ x) := by
  rw [IsNeutral] at hx ⊢
  rw [hx, map_neutral]

end NonabelianH1

end RiemannResearch.GaloisCohomology
