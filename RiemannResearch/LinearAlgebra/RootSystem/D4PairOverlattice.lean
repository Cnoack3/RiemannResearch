/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4PairDiscriminant

/-!
# Integral D4-by-D4 gluing overlattices

For a triality symmetry `τ`, this file takes the inverse image of its
discriminant graph under

`P ⊕ P → (P / Q) ⊕ (P / Q)`.

The resulting additive subgroup lies between `Q ⊕ Q` and `P ⊕ P`. Its
quotient by `Q ⊕ Q` is the four-element triality graph, and every vector in
it has even norm for the orthogonal sum of the two inverse-Cartan forms.

This is a concrete integral gluing overlattice. The file does not yet prove
unimodularity, identify the overlattice with E8, or construct a D4-by-D4
subgroup of an E8 group scheme.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

noncomputable section

/-- Weight coordinates for two orthogonal D4 copies. -/
abbrev PairWeightCoordinates :=
  WeightCoordinates × WeightCoordinates

/-- Reduction of two weight-coordinate vectors to the pair discriminant
group. -/
def pairDiscriminantMap :
    PairWeightCoordinates →+ PairDiscriminantGroup where
  toFun x :=
    (QuotientAddGroup.mk' rootSublattice x.1,
      QuotientAddGroup.mk' rootSublattice x.2)
  map_zero' := by
    simp
  map_add' x y := by
    simp

theorem pairDiscriminantMap_surjective :
    Function.Surjective pairDiscriminantMap := by
  rintro ⟨a, b⟩
  obtain ⟨x, rfl⟩ :=
    QuotientAddGroup.mk'_surjective rootSublattice a
  obtain ⟨y, rfl⟩ :=
    QuotientAddGroup.mk'_surjective rootSublattice b
  exact ⟨(x, y), rfl⟩

/-- The direct sum `Q ⊕ Q` inside pair weight coordinates. -/
def pairRootSublattice : AddSubgroup PairWeightCoordinates :=
  rootSublattice.prod rootSublattice

theorem pairRootSublattice_eq_pairDiscriminantMap_ker :
    pairRootSublattice = pairDiscriminantMap.ker := by
  ext x
  change
    (x.1 ∈ rootSublattice ∧ x.2 ∈ rootSublattice) ↔
      pairDiscriminantMap x = 0
  rw [Prod.ext_iff]
  simp only [pairDiscriminantMap]
  constructor
  · rintro ⟨hx, hy⟩
    constructor
    · exact (QuotientAddGroup.eq_zero_iff x.1).2 hx
    · exact (QuotientAddGroup.eq_zero_iff x.2).2 hy
  · rintro ⟨hx, hy⟩
    exact ⟨(QuotientAddGroup.eq_zero_iff x.1).1 hx,
      (QuotientAddGroup.eq_zero_iff x.2).1 hy⟩

/-- The integral overlattice obtained as the inverse image of a triality
discriminant graph. -/
def pairGluingOverlattice (τ : DiagramSymmetry) :
    AddSubgroup PairWeightCoordinates :=
  (discriminantGraph τ).comap pairDiscriminantMap

@[simp]
theorem mem_pairGluingOverlattice_iff
    (τ : DiagramSymmetry) (x : PairWeightCoordinates) :
    x ∈ pairGluingOverlattice τ ↔
      QuotientAddGroup.mk' rootSublattice x.2 =
        discriminantAction τ
          (QuotientAddGroup.mk' rootSublattice x.1) := by
  change pairDiscriminantMap x ∈ discriminantGraph τ ↔ _
  rw [mem_discriminantGraph_iff]
  rfl

theorem pairRootSublattice_le_pairGluingOverlattice
    (τ : DiagramSymmetry) :
    pairRootSublattice ≤ pairGluingOverlattice τ := by
  intro x hx
  change pairDiscriminantMap x ∈ discriminantGraph τ
  have hker : x ∈ pairDiscriminantMap.ker := by
    rw [← pairRootSublattice_eq_pairDiscriminantMap_ker]
    exact hx
  change pairDiscriminantMap x = 0 at hker
  rw [hker]
  exact (discriminantGraph τ).zero_mem

/-- The orthogonal-sum inverse-Cartan norm on pair weight coordinates. -/
def pairWeightNorm (x : PairWeightCoordinates) : ℤ :=
  weightNorm x.1 + weightNorm x.2

/-- Every vector in a triality gluing overlattice has even norm. -/
theorem two_dvd_pairWeightNorm_of_mem_pairGluingOverlattice
    (τ : DiagramSymmetry) {x : PairWeightCoordinates}
    (hx : x ∈ pairGluingOverlattice τ) :
    (2 : ℤ) ∣ pairWeightNorm x := by
  apply
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (pairWeightNorm x) 2).mp
  have hq :
      pairDiscriminantQuadratic (pairDiscriminantMap x) = 0 :=
    discriminantGraph_isotropic τ hx
  change
    discriminantQuadratic
        (QuotientAddGroup.mk' rootSublattice x.1) +
      discriminantQuadratic
        (QuotientAddGroup.mk' rootSublattice x.2) = 0 at hq
  rw [discriminantQuadratic_mk, discriminantQuadratic_mk] at hq
  simpa [pairWeightNorm] using hq

/-- The root sublattice, regarded inside its gluing overlattice. -/
def pairRootInGluing (τ : DiagramSymmetry) :
    AddSubgroup (pairGluingOverlattice τ) :=
  pairRootSublattice.comap (pairGluingOverlattice τ).subtype

/-- Reduction of a gluing-overlattice vector to the discriminant graph. -/
def gluingProjection (τ : DiagramSymmetry) :
    pairGluingOverlattice τ →+ discriminantGraph τ where
  toFun x := ⟨pairDiscriminantMap x.1, x.2⟩
  map_zero' := by
    apply Subtype.ext
    exact pairDiscriminantMap.map_zero
  map_add' x y := by
    apply Subtype.ext
    exact pairDiscriminantMap.map_add x.1 y.1

theorem gluingProjection_surjective (τ : DiagramSymmetry) :
    Function.Surjective (gluingProjection τ) := by
  rintro ⟨g, hg⟩
  obtain ⟨x, hx⟩ := pairDiscriminantMap_surjective g
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change pairDiscriminantMap x ∈ discriminantGraph τ
    rw [hx]
    exact hg
  · apply Subtype.ext
    exact hx

theorem pairRootInGluing_eq_gluingProjection_ker
    (τ : DiagramSymmetry) :
    pairRootInGluing τ = (gluingProjection τ).ker := by
  ext x
  constructor
  · intro hx
    apply Subtype.ext
    change pairDiscriminantMap x.1 = 0
    have hker : x.1 ∈ pairDiscriminantMap.ker := by
      rw [← pairRootSublattice_eq_pairDiscriminantMap_ker]
      exact hx
    exact hker
  · intro hx
    change x.1 ∈ pairRootSublattice
    rw [pairRootSublattice_eq_pairDiscriminantMap_ker]
    change pairDiscriminantMap x.1 = 0
    exact congrArg Subtype.val hx

/-- The quotient of a triality gluing overlattice by `Q ⊕ Q`. -/
abbrev PairGluingQuotient (τ : DiagramSymmetry) :=
  (pairGluingOverlattice τ) ⧸ pairRootInGluing τ

/-- The gluing quotient is exactly the chosen discriminant graph. -/
noncomputable def pairGluingQuotientEquivGraph
    (τ : DiagramSymmetry) :
    PairGluingQuotient τ ≃+ discriminantGraph τ :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (pairRootInGluing_eq_gluingProjection_ker τ)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (gluingProjection τ) (gluingProjection_surjective τ))

/-- Equivalently, the gluing quotient is one D4 discriminant group. -/
noncomputable def pairGluingQuotientEquivDiscriminant
    (τ : DiagramSymmetry) :
    PairGluingQuotient τ ≃+ DiscriminantGroup :=
  (pairGluingQuotientEquivGraph τ).trans
    (discriminantGroupEquivGraph τ).symm

/-- Every triality gluing overlattice contains `Q ⊕ Q` with quotient of
order four. -/
theorem natCard_pairGluingQuotient (τ : DiagramSymmetry) :
    Nat.card (PairGluingQuotient τ) = 4 := by
  rw [Nat.card_congr
    (pairGluingQuotientEquivDiscriminant τ).toEquiv]
  exact natCard_discriminantGroup

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
