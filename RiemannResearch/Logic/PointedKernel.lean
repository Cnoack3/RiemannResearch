/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic

/-!
# Trivial fibers of pointed maps

This module isolates the exact pointed-set logic used when restriction maps are
iterated through a tower. A trivial kernel here means a trivial fiber over the
distinguished point; it is deliberately weaker than injectivity of the entire
map.
-/

namespace RiemannResearch.Logic

/-- The fiber of `f` over `b₀` consists exactly of `a₀`. -/
def HasTrivialKernel {A B : Type*} (a₀ : A) (b₀ : B) (f : A → B) : Prop :=
  ∀ a, f a = b₀ ↔ a = a₀

/-- A map with trivial pointed kernel preserves the distinguished point. -/
theorem HasTrivialKernel.map_basepoint
    {A B : Type*} {a₀ : A} {b₀ : B} {f : A → B}
    (hf : HasTrivialKernel a₀ b₀ f) :
    f a₀ = b₀ :=
  (hf a₀).2 rfl

/-- Trivial pointed kernels compose. This is the abstract iteration step used
for cyclic restriction-kernel theorems along solvable towers. -/
theorem HasTrivialKernel.comp
    {A B C : Type*}
    {a₀ : A} {b₀ : B} {c₀ : C}
    {f : A → B} {g : B → C}
    (hf : HasTrivialKernel a₀ b₀ f)
    (hg : HasTrivialKernel b₀ c₀ g) :
    HasTrivialKernel a₀ c₀ (g ∘ f) := by
  intro a
  rw [Function.comp_apply, hg, hf]

/-- Exactness at the distinguished point of the right-hand type: the fiber of
`g` over `c₀` is exactly the range of `f`. -/
def IsPointedExact {A B C : Type*}
    (c₀ : C) (f : A → B) (g : B → C) : Prop :=
  ∀ b, g b = c₀ ↔ ∃ a, f a = b

/-- In a pointed exact pair, the second map has trivial kernel when the source
of the first map is a subsingleton. -/
theorem IsPointedExact.hasTrivialKernel_of_subsingleton_left
    {A B C : Type*}
    {a₀ : A} {b₀ : B} {c₀ : C}
    {f : A → B} {g : B → C}
    (hExact : IsPointedExact c₀ f g)
    [Subsingleton A] (hf : f a₀ = b₀) :
    HasTrivialKernel b₀ c₀ g := by
  intro b
  constructor
  · intro hgb
    obtain ⟨a, ha⟩ := (hExact b).mp hgb
    calc
      b = f a := ha.symm
      _ = f a₀ := congrArg f (Subsingleton.elim a a₀)
      _ = b₀ := hf
  · intro hb
    subst b
    exact (hExact b₀).mpr ⟨a₀, hf⟩

/-- In a pointed exact pair, the first map is surjective when the target of
the second map is a subsingleton. -/
theorem IsPointedExact.surjective_left_of_subsingleton_right
    {A B C : Type*} {c₀ : C}
    {f : A → B} {g : B → C}
    (hExact : IsPointedExact c₀ f g)
    [Subsingleton C] :
    Function.Surjective f := by
  intro b
  exact (hExact b).mp (Subsingleton.elim _ _)

/-- The range of a pointed map from a subsingleton type consists exactly of
the distinguished target point. -/
theorem exists_map_eq_iff_eq_basepoint_of_subsingleton
    {A B : Type*} {a₀ : A} {b₀ b : B}
    {f : A → B} [Subsingleton A] (hf : f a₀ = b₀) :
    (∃ a, f a = b) ↔ b = b₀ := by
  constructor
  · rintro ⟨a, rfl⟩
    exact (congrArg f (Subsingleton.elim a a₀)).trans hf
  · rintro rfl
    exact ⟨a₀, hf⟩

/-- A map with trivial pointed kernel has a subsingleton domain when its
codomain is a subsingleton. -/
theorem HasTrivialKernel.subsingleton_domain_of_subsingleton_codomain
    {A B : Type*} {a₀ : A} {b₀ : B} {f : A → B}
    (hf : HasTrivialKernel a₀ b₀ f) [Subsingleton B] :
    Subsingleton A := by
  refine ⟨fun a a' => ?_⟩
  have ha : a = a₀ := (hf a).mp (Subsingleton.elim _ _)
  have ha' : a' = a₀ := (hf a').mp (Subsingleton.elim _ _)
  exact ha.trans ha'.symm

/-- Transport a trivial pointed boundary fiber through a twisting equivalence.
When the transported boundary vanishes exactly when an invariant agrees with
its basepoint value, equality of invariants detects the basepoint. -/
theorem HasTrivialKernel.invariant_eq_iff_of_twist
    {A B C D : Type*}
    {a₀ : A} {b₀ : B} {c₀ : C}
    {boundary : A → C} {invariant : B → D}
    (twist : A ≃ B)
    (hkernel : HasTrivialKernel a₀ c₀ boundary)
    (htwist : twist a₀ = b₀)
    (hcompat : ∀ b, boundary (twist.symm b) = c₀ ↔
      invariant b = invariant b₀) :
    ∀ b, invariant b = invariant b₀ ↔ b = b₀ := by
  intro b
  constructor
  · intro hb
    have ha : twist.symm b = a₀ :=
      (hkernel (twist.symm b)).1 ((hcompat b).2 hb)
    calc
      b = twist (twist.symm b) := (twist.apply_symm_apply b).symm
      _ = twist a₀ := congrArg twist ha
      _ = b₀ := htwist
  · rintro rfl
    rfl

/-- Pull pointed exactness up a commutative diagram along an injective
vertical map. The top composite is required explicitly. -/
theorem IsPointedExact.of_injective_vertical
    {A B C D E : Type*}
    {c₀ : C} {e₀ : E}
    {f : A → B} {g : B → C}
    {f' : A → D} {g' : D → E}
    {i : B → D} {j : C → E}
    (hi : Function.Injective i)
    (hfcomm : ∀ a, i (f a) = f' a)
    (hgcomm : ∀ b, j (g b) = g' (i b))
    (hj₀ : j c₀ = e₀)
    (hbottom : IsPointedExact e₀ f' g')
    (hcomplex : ∀ a, g (f a) = c₀) :
    IsPointedExact c₀ f g := by
  intro b
  constructor
  · intro hb
    have hzero : g' (i b) = e₀ := by
      rw [← hgcomm b, hb, hj₀]
    rcases (hbottom (i b)).1 hzero with ⟨a, ha⟩
    refine ⟨a, hi ?_⟩
    exact (hfcomm a).trans ha
  · rintro ⟨a, rfl⟩
    exact hcomplex a

universe u

/-- The composite through the first `n` arrows of a dependent tower. -/
def towerMap {A : Nat → Type u}
    (step : ∀ n, A n → A (n + 1)) :
    ∀ n, A 0 → A n
  | 0 => id
  | n + 1 => step n ∘ towerMap step n

@[simp]
theorem towerMap_zero {A : Nat → Type u}
    (step : ∀ n, A n → A (n + 1)) :
    towerMap step 0 = id :=
  rfl

@[simp]
theorem towerMap_succ {A : Nat → Type u}
    (step : ∀ n, A n → A (n + 1)) (n : Nat) :
    towerMap step (n + 1) = step n ∘ towerMap step n :=
  rfl

/-- Trivial pointed kernels iterate through an arbitrary finite dependent
tower. This packages the exact logical step used to iterate cyclic
restriction-kernel theorems along a solvable composition series. -/
theorem HasTrivialKernel.tower
    {A : Nat → Type u}
    (base : ∀ n, A n)
    (step : ∀ n, A n → A (n + 1))
    (hstep : ∀ n, HasTrivialKernel (base n) (base (n + 1)) (step n)) :
    ∀ n, HasTrivialKernel (base 0) (base n) (towerMap step n) := by
  intro n
  induction n with
  | zero =>
      intro a
      simp [towerMap]
  | succ n ih =>
      exact ih.comp (hstep n)

end RiemannResearch.Logic
