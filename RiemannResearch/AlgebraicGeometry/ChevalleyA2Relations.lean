/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.ChevalleyRankOneRootSubgroups

/-!
# Integral type-A2 Chevalley relations in `SL₃`

This file constructs the three positive root subgroups of the standard
type-A2 subsystem in split `SL₃` over every commutative ring.  It proves their
injectivity and base-change naturality, the two commuting relations involving
the highest root, and the genuine Chevalley product and commutator formulas

`x₁₂(s) x₂₃(t) = x₂₃(t) x₁₃(st) x₁₂(s)`

and

`[x₁₂(s), x₂₃(t)] = x₁₃(st)`,

where the displayed commutator is expanded explicitly in the theorem
statement.

These are pointwise integral matrix identities, not a supplied relation
interface.  They provide the first rank-two simply-laced relation needed by a
future Chevalley construction of split E8.  This file does not yet construct
the coordinate Hopf algebra of `SL₃` or of E8.
-/

namespace RiemannResearch
namespace AlgebraicGeometry
namespace ChevalleyA2

open ChevalleyRankOne

variable (S : Type) [CommRing S]

/-- The split rank-three special linear group used for the type-A2 model. -/
abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) S

/-- The simple positive root `e₁-e₂`. -/
def root12 : Multiplicative S →* SL3 S :=
  transvectionRoot S (0 : Fin 3) 1 (by decide)

/-- The simple positive root `e₂-e₃`. -/
def root23 : Multiplicative S →* SL3 S :=
  transvectionRoot S (1 : Fin 3) 2 (by decide)

/-- The highest positive root `e₁-e₃`. -/
def root13 : Multiplicative S →* SL3 S :=
  transvectionRoot S (0 : Fin 3) 2 (by decide)

theorem root12_injective : Function.Injective (root12 S) :=
  transvectionRoot_injective S (0 : Fin 3) 1 (by decide)

theorem root23_injective : Function.Injective (root23 S) :=
  transvectionRoot_injective S (1 : Fin 3) 2 (by decide)

theorem root13_injective : Function.Injective (root13 S) :=
  transvectionRoot_injective S (0 : Fin 3) 2 (by decide)

variable {T : Type} [CommRing T]

theorem root12_natural (f : S →+* T) (t : Multiplicative S) :
    Matrix.SpecialLinearGroup.map f (root12 S t) =
      root12 T (f.toAddMonoidHom.toMultiplicative t) :=
  transvectionRoot_natural S f (0 : Fin 3) 1 (by decide) t

theorem root23_natural (f : S →+* T) (t : Multiplicative S) :
    Matrix.SpecialLinearGroup.map f (root23 S t) =
      root23 T (f.toAddMonoidHom.toMultiplicative t) :=
  transvectionRoot_natural S f (1 : Fin 3) 2 (by decide) t

theorem root13_natural (f : S →+* T) (t : Multiplicative S) :
    Matrix.SpecialLinearGroup.map f (root13 S t) =
      root13 T (f.toAddMonoidHom.toMultiplicative t) :=
  transvectionRoot_natural S f (0 : Fin 3) 2 (by decide) t

@[simp] theorem root12_inv (s : S) :
    (root12 S (Multiplicative.ofAdd s))⁻¹ =
      root12 S (Multiplicative.ofAdd (-s)) := by
  rw [← map_inv]
  rfl

@[simp] theorem root23_inv (t : S) :
    (root23 S (Multiplicative.ofAdd t))⁻¹ =
      root23 S (Multiplicative.ofAdd (-t)) := by
  rw [← map_inv]
  rfl

@[simp] theorem root13_inv (t : S) :
    (root13 S (Multiplicative.ofAdd t))⁻¹ =
      root13 S (Multiplicative.ofAdd (-t)) := by
  rw [← map_inv]
  rfl

/-- The roots `e₁-e₂` and `e₁-e₃` commute. -/
theorem root12_root13_commute (s t : S) :
    root12 S (Multiplicative.ofAdd s) *
        root13 S (Multiplicative.ofAdd t) =
      root13 S (Multiplicative.ofAdd t) *
        root12 S (Multiplicative.ofAdd s) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  change
    (Matrix.transvection (0 : Fin 3) 1 s *
      Matrix.transvection (0 : Fin 3) 2 t) i j =
    (Matrix.transvection (0 : Fin 3) 2 t *
      Matrix.transvection (0 : Fin 3) 1 s) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.transvection, Matrix.single, Matrix.one_apply]

/-- The roots `e₁-e₃` and `e₂-e₃` commute. -/
theorem root13_root23_commute (s t : S) :
    root13 S (Multiplicative.ofAdd s) *
        root23 S (Multiplicative.ofAdd t) =
      root23 S (Multiplicative.ofAdd t) *
        root13 S (Multiplicative.ofAdd s) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  change
    (Matrix.transvection (0 : Fin 3) 2 s *
      Matrix.transvection (1 : Fin 3) 2 t) i j =
    (Matrix.transvection (1 : Fin 3) 2 t *
      Matrix.transvection (0 : Fin 3) 2 s) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.transvection, Matrix.single, Matrix.one_apply]

/-- The positive type-A2 Chevalley product relation. -/
theorem positive_product_relation (s t : S) :
    root12 S (Multiplicative.ofAdd s) *
        root23 S (Multiplicative.ofAdd t) =
      root23 S (Multiplicative.ofAdd t) *
        root13 S (Multiplicative.ofAdd (s * t)) *
        root12 S (Multiplicative.ofAdd s) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  change
    (Matrix.transvection (0 : Fin 3) 1 s *
      Matrix.transvection (1 : Fin 3) 2 t) i j =
    ((Matrix.transvection (1 : Fin 3) 2 t *
      Matrix.transvection (0 : Fin 3) 2 (s * t)) *
      Matrix.transvection (0 : Fin 3) 1 s) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.transvection, Matrix.single, Matrix.one_apply]

/-- The positive type-A2 Chevalley commutator relation, with the commutator
expanded using the convention `x y x⁻¹ y⁻¹`. -/
theorem positive_commutator_relation (s t : S) :
    root12 S (Multiplicative.ofAdd s) *
        root23 S (Multiplicative.ofAdd t) *
        (root12 S (Multiplicative.ofAdd s))⁻¹ *
        (root23 S (Multiplicative.ofAdd t))⁻¹ =
      root13 S (Multiplicative.ofAdd (s * t)) := by
  rw [root12_inv, root23_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  repeat' rw [Matrix.SpecialLinearGroup.coe_mul]
  change
    (((Matrix.transvection (0 : Fin 3) 1 s *
      Matrix.transvection (1 : Fin 3) 2 t) *
      Matrix.transvection (0 : Fin 3) 1 (-s)) *
      Matrix.transvection (1 : Fin 3) 2 (-t)) i j =
    Matrix.transvection (0 : Fin 3) 2 (s * t) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.transvection, Matrix.single, Matrix.one_apply]

end ChevalleyA2
end AlgebraicGeometry
end RiemannResearch
