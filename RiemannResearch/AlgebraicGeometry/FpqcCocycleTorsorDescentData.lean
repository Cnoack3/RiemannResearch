/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FpqcCechH1

/-!
# Fixed-cover regular-torsor descent data from a Čech cocycle

This module packages the first bounded reverse step from a represented-
presheaf one-cocycle toward an fpqc torsor.

Over a generalized point `a : T ⟶ U i`, the local regular left torsor has
fiber `G(T)`. A cocycle component `γᵢⱼ` gives the transition from chart
`i` to chart `j` by right translation `x ↦ x * γᵢⱼ`. Right translation
is left-equivariant, and composition agrees with Mathlib's convention
`γᵢⱼ * γⱼₖ = γᵢₖ`.

The package records restriction naturality, equivariance, diagonal identity,
inverse, and triple-overlap composition. It does not construct a descended
scheme or module object, assert effective fpqc descent, produce a global
torsor, or construct `FpqcH1TorsorClassifier`.

Source: user-provided continuation handoff and Mathlib's
`PresheafOfGroups.OneCocycle` API.
-/

open CategoryTheory

universe u v w w'

noncomputable section

namespace CategoryTheory.PresheafOfGroups

variable {C : Type u} [Category.{v} C]
variable {G : Cᵒᵖ ⥤ GrpCat.{w}} {I : Type w'} {U : I → C}

/-- The fiber of the regular left G-torsor on chart U i. -/
abbrev RegularLocalTorsor
    (G : Cᵒᵖ ⥤ GrpCat.{w}) (U : I → C) (i : I)
    {T : C} (_a : T ⟶ U i) : Type w :=
  G.obj (Opposite.op T)

/-- Generalized-point descent data for regular left torsors on a fixed
covering family. Transitions are oriented from i to j. -/
structure RegularTorsorDescentData
    (G : Cᵒᵖ ⥤ GrpCat.{w}) (U : I → C) where
  /-- The transition equivalence on a generalized pairwise overlap. -/
  transition :
    ∀ (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j),
      RegularLocalTorsor G U i a ≃ RegularLocalTorsor G U j b
  /-- Transitions commute with restriction of generalized overlap points. -/
  transition_precomp :
    ∀ (i j : I) {T T' : C} (φ : T ⟶ T')
      (a : T' ⟶ U i) (b : T' ⟶ U j)
      (x : RegularLocalTorsor G U i a),
      G.map φ.op (transition i j a b x) =
        transition i j (φ ≫ a) (φ ≫ b) (G.map φ.op x)
  /-- Every transition is equivariant for the regular left action. -/
  transition_equivariant :
    ∀ (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j)
      (g x : RegularLocalTorsor G U i a),
      transition i j a b (g * x) = g * transition i j a b x
  /-- A transition restricted to the diagonal is the identity. -/
  transition_refl :
    ∀ (i : I) {T : C} (a : T ⟶ U i),
      transition i i a a = Equiv.refl _
  /-- Reversing an overlap gives the inverse transition. -/
  transition_symm :
    ∀ (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j),
      (transition i j a b).symm = transition j i b a
  /-- Transitions compose on generalized triple overlaps. -/
  transition_trans :
    ∀ (i j k : I) {T : C}
      (a : T ⟶ U i) (b : T ⟶ U j) (c : T ⟶ U k),
      (transition i j a b).trans (transition j k b c) =
        transition i k a c

/-- The cocycle-induced transition from chart i to chart j. Right
multiplication makes it equivariant for the regular left action. -/
def OneCocycle.regularTransition
    (γ : OneCocycle G U) (i j : I) {T : C}
    (a : T ⟶ U i) (b : T ⟶ U j) :
    RegularLocalTorsor G U i a ≃ RegularLocalTorsor G U j b :=
  Equiv.mulRight (γ.ev i j a b)

/-- A regular transition acts by right multiplication. -/
@[simp] theorem OneCocycle.regularTransition_apply
    (γ : OneCocycle G U) (i j : I) {T : C}
    (a : T ⟶ U i) (b : T ⟶ U j)
    (x : RegularLocalTorsor G U i a) :
    γ.regularTransition i j a b x = x * γ.ev i j a b :=
  rfl

/-- Regular transitions commute with restriction of generalized points. -/
theorem OneCocycle.regularTransition_precomp
    (γ : OneCocycle G U) (i j : I) {T T' : C}
    (φ : T ⟶ T') (a : T' ⟶ U i) (b : T' ⟶ U j)
    (x : RegularLocalTorsor G U i a) :
    G.map φ.op (γ.regularTransition i j a b x) =
      γ.regularTransition i j (φ ≫ a) (φ ≫ b) (G.map φ.op x) := by
  change G.map φ.op (x * γ.ev i j a b) =
    G.map φ.op x * γ.ev i j (φ ≫ a) (φ ≫ b)
  rw [map_mul, γ.ev_precomp]

/-- Regular transitions are equivariant for the regular left action. -/
theorem OneCocycle.regularTransition_equivariant
    (γ : OneCocycle G U) (i j : I) {T : C}
    (a : T ⟶ U i) (b : T ⟶ U j)
    (g x : RegularLocalTorsor G U i a) :
    γ.regularTransition i j a b (g * x) =
      g * γ.regularTransition i j a b x := by
  simp only [regularTransition_apply, mul_assoc]

/-- A regular transition is the identity on the diagonal. -/
@[simp] theorem OneCocycle.regularTransition_refl
    (γ : OneCocycle G U) (i : I) {T : C} (a : T ⟶ U i) :
    γ.regularTransition i i a a = Equiv.refl _ := by
  ext x
  simp [regularTransition]

/-- Swapping the overlap legs gives the inverse transition. -/
theorem OneCocycle.regularTransition_symm
    (γ : OneCocycle G U) (i j : I) {T : C}
    (a : T ⟶ U i) (b : T ⟶ U j) :
    (γ.regularTransition i j a b).symm =
      γ.regularTransition j i b a := by
  ext x
  change x * (γ.ev i j a b)⁻¹ = x * γ.ev j i b a
  rw [OneCocycle.ev_symm G U γ i j a b, inv_inv]

/-- Regular transitions compose in cocycle order.
The proof uses γᵢⱼ * γⱼₖ = γᵢₖ. -/
theorem OneCocycle.regularTransition_trans
    (γ : OneCocycle G U) (i j k : I) {T : C}
    (a : T ⟶ U i) (b : T ⟶ U j) (c : T ⟶ U k) :
    (γ.regularTransition i j a b).trans
        (γ.regularTransition j k b c) =
      γ.regularTransition i k a c := by
  ext x
  change (x * γ.ev i j a b) * γ.ev j k b c =
    x * γ.ev i k a c
  rw [mul_assoc, γ.ev_trans]

/-- A one-cocycle packages all fixed-cover regular-torsor transition laws. -/
def OneCocycle.regularTorsorDescentData
    (γ : OneCocycle G U) : RegularTorsorDescentData G U where
  transition := γ.regularTransition
  transition_precomp := γ.regularTransition_precomp
  transition_equivariant := γ.regularTransition_equivariant
  transition_refl := γ.regularTransition_refl
  transition_symm := γ.regularTransition_symm
  transition_trans := γ.regularTransition_trans

end CategoryTheory.PresheafOfGroups

namespace RiemannResearch.AlgebraicGeometry

/-- Fixed-cover regular-torsor descent data for an affine group scheme. -/
abbrev FpqcRegularTorsorDescentData
    (R A : CommRingCat.{u}) [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover R I) :=
  PresheafOfGroups.RegularTorsorDescentData
    (affineGroupPresheaf R A) U.obj

/-- An affine-group one-cocycle determines fixed-cover regular-torsor
descent data. No effectiveness assertion is made. -/
def affineGroupCocycleTorsorDescentData
    (R A : CommRingCat.{u}) [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover R I)
    (γ : PresheafOfGroups.OneCocycle
      (affineGroupPresheaf R A) U.obj) :
    FpqcRegularTorsorDescentData R A U :=
  γ.regularTorsorDescentData

end RiemannResearch.AlgebraicGeometry
