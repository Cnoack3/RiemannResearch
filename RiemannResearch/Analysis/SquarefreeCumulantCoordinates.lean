/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring

/-!
# Finite squarefree cumulant coordinates

Source: the user's lattice and convolution-function proposal, 18 October 2026.
For squarefree moment/cumulant terminology, see T. Sinclair, *Finite free
convolution via reproducing kernels and squarefree algebras*, arXiv:2606.10870v2,
Section 4. The explicit unit-linear degree-three coordinate calculation and
its synthesis consumers are developed here; no novelty claim is made.

These finite polynomial identities preserve the exact synthesized set. They
do not supply an infinite-dimensional convergence theorem or a physical
primitive-energy bound. No identification of formal convolution multiplication
with an unrestricted physical operator product is used.
-/

namespace RiemannResearch.Analysis.SquarefreeCumulantCoordinates

/-- A surjective coordinate change preserves the exact set of synthesized vectors. -/
theorem range_reparam_eq {A B H : Type*} (synth : B → H) (reparam : A → B)
    (hreparam : Function.Surjective reparam) :
    Set.range (fun a => synth (reparam a)) = Set.range synth := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨reparam a, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hreparam b
    exact ⟨a, rfl⟩

/-- In particular, every finite objective predicate is invariant. -/
theorem exists_reparam_iff {A B H : Type*} (synth : B → H) (reparam : A → B)
    (hreparam : Function.Surjective reparam) (P : H → Prop) :
    (∃ a, P (synth (reparam a))) ↔ ∃ b, P (synth b) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨reparam a, ha⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := hreparam b
    exact ⟨a, hb⟩

/-- Coefficients indexed by nonempty subsets of a three-element Boolean lattice. -/
structure Coefficients3 (R : Type*) where
  x1 : R
  x2 : R
  x3 : R
  x12 : R
  x13 : R
  x23 : R
  x123 : R

variable {R : Type*} [CommRing R]

/-- The degree-three unit-linear functional calculus. For `f(z)=z+a₂z²+a₃z³`,
use `t=2*a₂` and `s=6*a₃` in the squarefree convolution algebra. -/
def triangular3 (t s : R) (c : Coefficients3 R) : Coefficients3 R where
  x1 := c.x1
  x2 := c.x2
  x3 := c.x3
  x12 := c.x12 + t * c.x1 * c.x2
  x13 := c.x13 + t * c.x1 * c.x3
  x23 := c.x23 + t * c.x2 * c.x3
  x123 := c.x123 + t * (c.x1 * c.x23 + c.x2 * c.x13 + c.x3 * c.x12) +
    s * c.x1 * c.x2 * c.x3

theorem triangular3_comp (t s u v : R) (c : Coefficients3 R) :
    triangular3 u v (triangular3 t s c) =
      triangular3 (t + u) (s + v + 3 * u * t) c := by
  cases c
  dsimp [triangular3]
  congr 1 <;> ring

theorem triangular3_left_inverse (t s : R) (c : Coefficients3 R) :
    triangular3 (-t) (3 * t ^ 2 - s) (triangular3 t s c) = c := by
  cases c
  dsimp [triangular3]
  congr 1 <;> ring

theorem triangular3_right_inverse (t s : R) (c : Coefficients3 R) :
    triangular3 t s (triangular3 (-t) (3 * t ^ 2 - s) c) = c := by
  cases c
  dsimp [triangular3]
  congr 1 <;> ring

/-- The finite polynomial coordinate equivalence requires no analytic convergence. -/
def triangularEquiv3 (t s : R) : Coefficients3 R ≃ Coefficients3 R where
  toFun := triangular3 t s
  invFun := triangular3 (-t) (3 * t ^ 2 - s)
  left_inv := triangular3_left_inverse t s
  right_inv := triangular3_right_inverse t s

/-- Nonempty coefficients of `exp_*(c)`, whose constant coefficient is one. -/
def squarefreeExp3 : Coefficients3 R → Coefficients3 R := triangular3 1 1

/-- Nonempty coefficients of `log_*(1+c)`, whose constant coefficient is zero. -/
def squarefreeLog3 : Coefficients3 R → Coefficients3 R := triangular3 (-1) 2

theorem squarefreeLog3_exp (c : Coefficients3 R) :
    squarefreeLog3 (squarefreeExp3 c) = c := by
  cases c
  dsimp [squarefreeLog3, squarefreeExp3, triangular3]
  congr 1 <;> ring

theorem squarefreeExp3_log (c : Coefficients3 R) :
    squarefreeExp3 (squarefreeLog3 c) = c := by
  cases c
  dsimp [squarefreeLog3, squarefreeExp3, triangular3]
  congr 1 <;> ring

theorem squarefreeExp3_surjective : Function.Surjective (squarefreeExp3 (R := R)) := by
  intro c
  exact ⟨squarefreeLog3 c, squarefreeExp3_log c⟩

theorem range_triangular3_eq {H : Type*} (synth : Coefficients3 R → H) (t s : R) :
    Set.range (fun c => synth (triangular3 t s c)) = Set.range synth :=
  range_reparam_eq synth _ (triangularEquiv3 t s).surjective

theorem range_squarefreeExp3_eq {H : Type*} (synth : Coefficients3 R → H) :
    Set.range (fun c => synth (squarefreeExp3 c)) = Set.range synth :=
  range_reparam_eq synth _ squarefreeExp3_surjective

theorem exists_squarefreeExp3_iff {H : Type*} (synth : Coefficients3 R → H)
    (P : H → Prop) :
    (∃ c, P (synth (squarefreeExp3 c))) ↔ ∃ c, P (synth c) :=
  exists_reparam_iff synth _ squarefreeExp3_surjective P

/-- Physical synthesis keeps the seven actual atoms and all coefficient signs. -/
def synthesize3 {H : Type*} [AddCommGroup H] [Module R H]
    (atoms : Coefficients3 H) (c : Coefficients3 R) : H :=
  c.x1 • atoms.x1 + c.x2 • atoms.x2 + c.x3 • atoms.x3 +
  c.x12 • atoms.x12 + c.x13 • atoms.x13 + c.x23 • atoms.x23 +
  c.x123 • atoms.x123

theorem synthesize3_mem {H : Type*} [AddCommGroup H] [Module R H]
    (S : Submodule R H) (atoms : Coefficients3 H) (c : Coefficients3 R)
    (h1 : atoms.x1 ∈ S) (h2 : atoms.x2 ∈ S) (h3 : atoms.x3 ∈ S)
    (h12 : atoms.x12 ∈ S) (h13 : atoms.x13 ∈ S) (h23 : atoms.x23 ∈ S)
    (h123 : atoms.x123 ∈ S) : synthesize3 atoms c ∈ S := by
  exact S.add_mem
    (S.add_mem
      (S.add_mem
        (S.add_mem
          (S.add_mem
            (S.add_mem (S.smul_mem _ h1) (S.smul_mem _ h2))
            (S.smul_mem _ h3))
          (S.smul_mem _ h12))
        (S.smul_mem _ h13))
      (S.smul_mem _ h23))
    (S.smul_mem _ h123)

end RiemannResearch.Analysis.SquarefreeCumulantCoordinates
