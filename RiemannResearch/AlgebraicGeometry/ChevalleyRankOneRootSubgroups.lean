/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Pointwise Chevalley transvection root subgroups

This file constructs the genuine transvection root homomorphisms
`Multiplicative S →* SLₙ(S)` over every commutative ring.  It proves that
they are injective and natural under base change.  The two rank-one
specializations give the positive and negative root subgroups of `SL₂`.

This is point-level Chevalley infrastructure.  It does not yet construct the
coordinate Hopf algebra of `SL₂` or a split E8 group scheme.
-/

namespace RiemannResearch
namespace AlgebraicGeometry
namespace ChevalleyRankOne

universe u v w

variable {n : Type u} [DecidableEq n] [Fintype n]
variable (S : Type v) [CommRing S]

/-- The special linear group used as the target of a transvection root. -/
abbrev SpecialLinear := Matrix.SpecialLinearGroup n S

/-- The determinant-one transvection with parameter `t`. -/
def transvectionRootPoint
    (i j : n) (hij : i ≠ j) (t : S) :
    SpecialLinear (n := n) S :=
  ⟨Matrix.transvection i j t,
    Matrix.det_transvection_of_ne i j hij t⟩

/-- A transvection is additive in its parameter, hence defines a group
homomorphism from the multiplicative re-tagging of the additive group. -/
def transvectionRoot (i j : n) (hij : i ≠ j) :
    Multiplicative S →* SpecialLinear (n := n) S where
  toFun t := transvectionRootPoint S i j hij t.toAdd
  map_one' := by
    apply Subtype.ext
    exact Matrix.transvection_zero i j
  map_mul' x y := by
    apply Subtype.ext
    exact (Matrix.transvection_mul_transvection_same
      i j hij x.toAdd y.toAdd).symm

@[simp]
theorem transvectionRootPoint_offdiag
    (i j : n) (hij : i ≠ j) (t : S) :
    ((transvectionRootPoint S i j hij t :
        SpecialLinear (n := n) S) : Matrix n n S) i j = t := by
  simp [transvectionRootPoint, Matrix.transvection, Matrix.single, hij]

/-- Distinct transvection parameters give distinct special-linear points. -/
theorem transvectionRoot_injective
    (i j : n) (hij : i ≠ j) :
    Function.Injective (transvectionRoot S i j hij) := by
  intro x y hxy
  have hentry := congrArg
    (fun g : SpecialLinear (n := n) S =>
      ((g : Matrix n n S) i j)) hxy
  change (Matrix.transvection i j x.toAdd) i j =
    (Matrix.transvection i j y.toAdd) i j at hentry
  have htoAdd : x.toAdd = y.toAdd := by
    simpa [Matrix.transvection, Matrix.single, hij] using hentry
  cases x with
  | ofAdd x =>
      cases y with
      | ofAdd y =>
          simpa using htoAdd

variable {T : Type w} [CommRing T]

/-- Transvection roots commute with arbitrary base change of commutative
rings. -/
theorem transvectionRoot_natural
    (f : S →+* T) (i j : n) (hij : i ≠ j)
    (t : Multiplicative S) :
    Matrix.SpecialLinearGroup.map f (transvectionRoot S i j hij t) =
      transvectionRoot T i j hij
        (f.toAddMonoidHom.toMultiplicative t) := by
  apply Subtype.ext
  change f.mapMatrix (Matrix.transvection i j t.toAdd) =
    Matrix.transvection i j (f t.toAdd)
  rw [Matrix.transvection, Matrix.transvection]
  rw [f.mapMatrix.map_add, f.mapMatrix.map_one]
  congr 1
  ext a b
  by_cases h : i = a ∧ j = b <;>
    simp [Matrix.single, h]

/-- The rank-one split special linear group. -/
abbrev SL2 (S : Type v) [CommRing S] :=
  Matrix.SpecialLinearGroup (Fin 2) S

/-- Positive rank-one root subgroup `t ↦ [[1,t],[0,1]]`. -/
def positiveRoot : Multiplicative S →* SL2 S :=
  transvectionRoot S (0 : Fin 2) 1 (by decide)

/-- Negative rank-one root subgroup `t ↦ [[1,0],[t,1]]`. -/
def negativeRoot : Multiplicative S →* SL2 S :=
  transvectionRoot S (1 : Fin 2) 0 (by decide)

theorem positiveRoot_injective :
    Function.Injective (positiveRoot S) :=
  transvectionRoot_injective S (0 : Fin 2) 1 (by decide)

theorem negativeRoot_injective :
    Function.Injective (negativeRoot S) :=
  transvectionRoot_injective S (1 : Fin 2) 0 (by decide)

theorem positiveRoot_natural
    (f : S →+* T) (t : Multiplicative S) :
    Matrix.SpecialLinearGroup.map f (positiveRoot S t) =
      positiveRoot T (f.toAddMonoidHom.toMultiplicative t) :=
  transvectionRoot_natural S f (0 : Fin 2) 1 (by decide) t

theorem negativeRoot_natural
    (f : S →+* T) (t : Multiplicative S) :
    Matrix.SpecialLinearGroup.map f (negativeRoot S t) =
      negativeRoot T (f.toAddMonoidHom.toMultiplicative t) :=
  transvectionRoot_natural S f (1 : Fin 2) 0 (by decide) t

end ChevalleyRankOne
end AlgebraicGeometry
end RiemannResearch
