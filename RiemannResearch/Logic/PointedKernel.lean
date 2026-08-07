/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
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

end RiemannResearch.Logic
