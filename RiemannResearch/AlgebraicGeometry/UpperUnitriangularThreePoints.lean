/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.ChevalleyA2CoordinateRelations

/-!
# The split upper-unitriangular group in rank two

This file gives the first genuine nonabelian unipotent model used by the
root-height program.  A point is stored in ordered-root coordinates
`(x₁₂,x₂₃,x₁₃)` and carries the Heisenberg multiplication

`(a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab')`.

The highest-root subgroup is central, equals the kernel of the projection to
the two simple-root coordinates, and the induced quotient is the additive
two-dimensional group.  The commutator is computed explicitly, and the group
is embedded faithfully into `SL₃` by the ordered product
`x₂₃(b)x₁₃(c)x₁₂(a)`.

Thus the height filtration has successive additive layers
`U/U₂ ≃ Gₐ²` and `U₂ ≃ Gₐ` at the level of points over every commutative ring.
-/

namespace RiemannResearch
namespace AlgebraicGeometry
namespace UpperUnitriangularThree

@[ext]
structure Point (S : Type) where
  root12 : S
  root23 : S
  root13 : S

namespace Point

variable {S : Type} [CommRing S]

instance : One (Point S) :=
  ⟨⟨0, 0, 0⟩⟩

instance : Mul (Point S) :=
  ⟨fun x y =>
    ⟨x.root12 + y.root12,
      x.root23 + y.root23,
      x.root13 + y.root13 + x.root12 * y.root23⟩⟩

instance : Inv (Point S) :=
  ⟨fun x =>
    ⟨-x.root12, -x.root23,
      -x.root13 + x.root12 * x.root23⟩⟩

@[simp] theorem one_root12 : (1 : Point S).root12 = 0 := rfl
@[simp] theorem one_root23 : (1 : Point S).root23 = 0 := rfl
@[simp] theorem one_root13 : (1 : Point S).root13 = 0 := rfl

@[simp] theorem mul_root12 (x y : Point S) :
    (x * y).root12 = x.root12 + y.root12 := rfl

@[simp] theorem mul_root23 (x y : Point S) :
    (x * y).root23 = x.root23 + y.root23 := rfl

@[simp] theorem mul_root13 (x y : Point S) :
    (x * y).root13 =
      x.root13 + y.root13 + x.root12 * y.root23 := rfl

@[simp] theorem inv_root12 (x : Point S) :
    x⁻¹.root12 = -x.root12 := rfl

@[simp] theorem inv_root23 (x : Point S) :
    x⁻¹.root23 = -x.root23 := rfl

@[simp] theorem inv_root13 (x : Point S) :
    x⁻¹.root13 = -x.root13 + x.root12 * x.root23 := rfl

instance : Group (Point S) where
  mul_assoc x y z := by
    ext <;> simp <;> ring
  one_mul x := by
    ext <;> simp
  mul_one x := by
    ext <;> simp
  inv_mul_cancel x := by
    ext <;> simp <;> ring

/-- The central highest-root point. -/
def center (c : S) : Point S := ⟨0, 0, c⟩

@[simp] theorem center_mul (c d : S) :
    center c * center d = center (c + d) := by
  ext <;> simp [center]

@[simp] theorem center_inv (c : S) :
    (center c)⁻¹ = center (-c) := by
  ext <;> simp [center]

theorem center_commute (c : S) (x : Point S) :
    center c * x = x * center c := by
  ext <;> simp [center] <;> ring

/-- Projection to the two height-one root coordinates. -/
def simpleProjection :
    Point S →* (Multiplicative S × Multiplicative S) where
  toFun x :=
    (Multiplicative.ofAdd x.root12, Multiplicative.ofAdd x.root23)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Embedding of the height-two highest-root subgroup. -/
def centerHom : Multiplicative S →* Point S where
  toFun c := center c.toAdd
  map_one' := rfl
  map_mul' c d := by
    ext <;> simp [center]

@[simp] theorem simpleProjection_center (c : S) :
    simpleProjection (center c) = 1 := rfl

@[simp] theorem mem_ker_simpleProjection_iff (x : Point S) :
    x ∈ MonoidHom.ker (simpleProjection (S := S)) ↔
      x.root12 = 0 ∧ x.root23 = 0 := by
  simp [simpleProjection]

theorem centerHom_injective :
    Function.Injective (centerHom (S := S)) := by
  intro c d h
  apply Multiplicative.toAdd.injective
  exact congrArg Point.root13 h

theorem simpleProjection_surjective :
    Function.Surjective (simpleProjection (S := S)) := by
  rintro ⟨a, b⟩
  refine ⟨⟨a.toAdd, b.toAdd, 0⟩, ?_⟩
  rfl

/-- The height-two root subgroup is exactly the kernel of the height-one
projection. -/
theorem ker_simpleProjection_eq_range_centerHom :
    MonoidHom.ker (simpleProjection (S := S)) =
      MonoidHom.range (centerHom (S := S)) := by
  ext x
  constructor
  · intro hx
    rw [mem_ker_simpleProjection_iff] at hx
    rcases hx with ⟨h12, h23⟩
    refine ⟨Multiplicative.ofAdd x.root13, ?_⟩
    ext <;> simp [centerHom, center, h12, h23]
  · rintro ⟨c, rfl⟩
    change simpleProjection (center c.toAdd) = 1
    exact simpleProjection_center c.toAdd

/-- First-isomorphism identification of the height-one quotient. -/
noncomputable def simpleQuotientEquiv :
    Point S ⧸ MonoidHom.ker (simpleProjection (S := S)) ≃*
      (Multiplicative S × Multiplicative S) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (simpleProjection (S := S)) simpleProjection_surjective

/-- The group commutator lands in the highest-root subgroup. -/
theorem commutator_formula (x y : Point S) :
    x * y * x⁻¹ * y⁻¹ =
      center (x.root12 * y.root23 - y.root12 * x.root23) := by
  ext <;> simp [center] <;> ring

theorem commutator_mem_center (x y : Point S) :
    x * y * x⁻¹ * y⁻¹ ∈
      MonoidHom.range (centerHom (S := S)) := by
  rw [commutator_formula]
  exact ⟨Multiplicative.ofAdd
    (x.root12 * y.root23 - y.root12 * x.root23), rfl⟩

/-- Ordered-root realization in the standard `SL₃`. -/
def toSL3 (x : Point S) : Matrix.SpecialLinearGroup (Fin 3) S :=
  ChevalleyA2.root23 S (Multiplicative.ofAdd x.root23) *
    ChevalleyA2.root13 S (Multiplicative.ofAdd x.root13) *
    ChevalleyA2.root12 S (Multiplicative.ofAdd x.root12)

@[simp] theorem toSL3_matrix (x : Point S) :
    ((toSL3 x : Matrix.SpecialLinearGroup (Fin 3) S) :
      Matrix (Fin 3) (Fin 3) S) =
      !![1, x.root12, x.root13; 0, 1, x.root23; 0, 0, 1] := by
  unfold toSL3 ChevalleyA2.root12 ChevalleyA2.root23 ChevalleyA2.root13
  ext i j
  repeat' rw [Matrix.SpecialLinearGroup.coe_mul]
  change
    ((Matrix.transvection (1 : Fin 3) 2 x.root23 *
      Matrix.transvection (0 : Fin 3) 2 x.root13) *
      Matrix.transvection (0 : Fin 3) 1 x.root12) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.transvection, Matrix.single, Matrix.one_apply]

/-- The ordered-root realization respects multiplication. -/
def toSL3Hom :
    Point S →* Matrix.SpecialLinearGroup (Fin 3) S where
  toFun := toSL3
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [toSL3_matrix, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [toSL3_matrix, Matrix.SpecialLinearGroup.coe_mul,
      toSL3_matrix, toSL3_matrix]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The upper-unitriangular parametrization is faithful. -/
theorem toSL3Hom_injective :
    Function.Injective (toSL3Hom (S := S)) := by
  intro x y h
  change toSL3 x = toSL3 y at h
  have hm := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 3) S =>
      (g : Matrix (Fin 3) (Fin 3) S)) h
  rw [toSL3_matrix, toSL3_matrix] at hm
  apply Point.ext
  · exact congrArg (fun m => m (0 : Fin 3) 1) hm
  · exact congrArg (fun m => m (1 : Fin 3) 2) hm
  · exact congrArg (fun m => m (0 : Fin 3) 2) hm

end Point
end UpperUnitriangularThree
end AlgebraicGeometry
end RiemannResearch
