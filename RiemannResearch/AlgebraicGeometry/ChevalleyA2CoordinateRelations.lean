/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SpecialLinearThreeRootSubgroupHopf

/-!
# Universal type-A2 Chevalley coordinate relations

The two independent additive parameters are carried by
`ℤ[X] ⊗[ℤ] ℤ[X]`.  Over this universal ring, this file proves the positive
type-A2 product and commutator formulas as equalities of `SL₃`-points and then
as equalities of coordinate-algebra morphisms out of `O(SL₃)`.

Consequently the relations hold before specialization to any field or ring.
This is the represented rank-two relation required by a genuine simply-laced
Chevalley construction.
-/

namespace RiemannResearch
namespace AlgebraicGeometry
namespace ChevalleyA2Coordinate

noncomputable section

open scoped TensorProduct

private abbrev A := SpecialLinearThree.Coordinate
private abbrev P := AdditiveGroup.Coordinate ℤ
private abbrev Q := P ⊗[ℤ] P

local instance parameterAddCommMonoid : AddCommMonoid P :=
  (inferInstance : Semiring P).toAddCommMonoid

local instance parameterIntModule : Module ℤ P :=
  @Algebra.toModule ℤ P _ _ (inferInstance : Algebra ℤ P)

/-- Inclusion of the first universal additive parameter. -/
def includeLeft : P →ₐ[ℤ] Q :=
  Algebra.TensorProduct.includeLeft

/-- Inclusion of the second universal additive parameter. -/
def includeRight : P →ₐ[ℤ] Q :=
  Algebra.TensorProduct.includeRight

/-- The first universal parameter. -/
def leftParameter : Q := includeLeft Polynomial.X

/-- The second universal parameter. -/
def rightParameter : Q := includeRight Polynomial.X

def root12Point : Matrix.SpecialLinearGroup (Fin 3) Q :=
  ChevalleyA2.root12 Q (Multiplicative.ofAdd leftParameter)

def root23Point : Matrix.SpecialLinearGroup (Fin 3) Q :=
  ChevalleyA2.root23 Q (Multiplicative.ofAdd rightParameter)

def root13ProductPoint : Matrix.SpecialLinearGroup (Fin 3) Q :=
  ChevalleyA2.root13 Q
    (Multiplicative.ofAdd (leftParameter * rightParameter))

/-- The left side `x₁₂(s)x₂₃(t)` of the universal product formula. -/
def leftProductPoint : Matrix.SpecialLinearGroup (Fin 3) Q :=
  root12Point * root23Point

/-- The right side `x₂₃(t)x₁₃(st)x₁₂(s)`. -/
def rightProductPoint : Matrix.SpecialLinearGroup (Fin 3) Q :=
  root23Point * root13ProductPoint * root12Point

/-- Universal positive type-A2 product relation. -/
theorem positiveProductPoint_relation :
    leftProductPoint = rightProductPoint := by
  exact ChevalleyA2.positive_product_relation
    Q leftParameter rightParameter

/-- Pullback associated to the left side of the product relation. -/
def leftProductAlgHom : A →ₐ[ℤ] Q :=
  SpecialLinearThree.coordinateAlgHomOfRingHom
    (SpecialLinearThree.coordinateEvaluation leftProductPoint)

/-- Pullback associated to the right side of the product relation. -/
def rightProductAlgHom : A →ₐ[ℤ] Q :=
  SpecialLinearThree.coordinateAlgHomOfRingHom
    (SpecialLinearThree.coordinateEvaluation rightProductPoint)

/-- The positive product formula is an equality of coordinate-algebra
morphisms over the universal two-parameter base. -/
theorem positiveProductAlgHom_relation :
    leftProductAlgHom = rightProductAlgHom := by
  unfold leftProductAlgHom rightProductAlgHom
  rw [positiveProductPoint_relation]

/-- The expanded commutator `x₁₂(s)x₂₃(t)x₁₂(s)⁻¹x₂₃(t)⁻¹`. -/
def commutatorPoint : Matrix.SpecialLinearGroup (Fin 3) Q :=
  root12Point * root23Point * root12Point⁻¹ * root23Point⁻¹

/-- Universal positive type-A2 commutator relation. -/
theorem positiveCommutatorPoint_relation :
    commutatorPoint = root13ProductPoint := by
  exact ChevalleyA2.positive_commutator_relation
    Q leftParameter rightParameter

/-- Pullback associated to the expanded commutator. -/
def commutatorAlgHom : A →ₐ[ℤ] Q :=
  SpecialLinearThree.coordinateAlgHomOfRingHom
    (SpecialLinearThree.coordinateEvaluation commutatorPoint)

/-- Pullback associated to the highest-root term `x₁₃(st)`. -/
def root13ProductAlgHom : A →ₐ[ℤ] Q :=
  SpecialLinearThree.coordinateAlgHomOfRingHom
    (SpecialLinearThree.coordinateEvaluation root13ProductPoint)

/-- The positive commutator formula is an equality of coordinate-algebra
morphisms over the universal two-parameter base. -/
theorem positiveCommutatorAlgHom_relation :
    commutatorAlgHom = root13ProductAlgHom := by
  unfold commutatorAlgHom root13ProductAlgHom
  rw [positiveCommutatorPoint_relation]

end

end ChevalleyA2Coordinate
end AlgebraicGeometry
end RiemannResearch
