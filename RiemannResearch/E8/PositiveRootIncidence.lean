/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E8.ConcreteRootVectorClassification

/-!
# Incidence among the concrete positive roots of E₈

This file extracts the rank-two incidence data needed for the positive-root
height filtration from the explicit 240-root certificate.  An ordered
`PositiveA2Pair` consists of positive roots whose inner product is `-1` in
ordinary coordinates, or `-4` in the doubled coordinates used here.

The finite proofs are kernel reductions through `decide`; they do not assume
an abstract root datum or a group-scheme provider.  Witness roots are decoded
structurally from their vector shapes rather than found by cubic search.

Source for the standard root-system incidence terminology: N. Bourbaki,
*Lie Groups and Lie Algebras*, Chapters 4--6, Planche VII.  The executable
coordinate certificates are proved directly in this module.
-/

namespace RiemannResearch
namespace E8
namespace ConcreteRootSystem

set_option maxRecDepth 100000

/-- Ordered positive-root pairs spanning a root subsystem of type `A₂`. -/
abbrev PositiveA2Pair :=
  {p : Root × Root //
    IsPositive p.1 ∧ IsPositive p.2 ∧
      dot (rootVector p.1) (rootVector p.2) = -4}

/-- Doubled-coordinate sum of two roots. -/
def addRootVectors (α β : Root) : Vector := fun i =>
  rootVector α i + rootVector β i

private def positiveA2PairFinset : Finset (Root × Root) :=
  (positiveRoots ×ˢ positiveRoots).filter fun p =>
    dot (rootVector p.1) (rootVector p.2) = -4

private theorem positiveA2PairFinset_spec (p : Root × Root) :
    p ∈ positiveA2PairFinset ↔
      IsPositive p.1 ∧ IsPositive p.2 ∧
        dot (rootVector p.1) (rootVector p.2) = -4 := by
  simp [positiveA2PairFinset, positiveRoots, and_assoc]

private def positiveA2PairEquiv :
    PositiveA2Pair ≃ ↥positiveA2PairFinset where
  toFun p := ⟨p.1, (positiveA2PairFinset_spec p.1).2 p.2⟩
  invFun p := ⟨p.1, (positiveA2PairFinset_spec p.1).1 p.2⟩
  left_inv _p := rfl
  right_inv _p := rfl

set_option maxHeartbeats 50000000 in
-- Exhaustive reduction over the 120-by-120 positive-root product.
private theorem card_positiveA2PairFinset :
    positiveA2PairFinset.card = 2240 := by
  decide

/-- There are 2,240 ordered positive `A₂` pairs. -/
theorem card_positiveA2Pairs :
    Fintype.card PositiveA2Pair = 2240 := by
  rw [Fintype.card_congr positiveA2PairEquiv, Fintype.card_coe]
  exact card_positiveA2PairFinset

private abbrev EnumeratedPositiveRoot := ↥positiveRoots

private theorem enumeratedPositiveRoot_isPositive
    (r : EnumeratedPositiveRoot) : IsPositive r.1 := by
  simpa [positiveRoots] using r.2

set_option maxHeartbeats 10000000 in
-- Search only for existence; uniqueness follows from `rootVector_injective`.
private theorem simpleRoot_exists :
    ∀ i : Fin 8, ∃ r : Root, rootVector r = simpleRoot i := by
  decide

/-- Each displayed simple root has a unique concrete root representative. -/
theorem existsUnique_rootVector_eq_simpleRoot (i : Fin 8) :
    ∃! r : Root, rootVector r = simpleRoot i := by
  obtain ⟨r, hr⟩ := simpleRoot_exists i
  refine ⟨r, hr, ?_⟩
  intro s hs
  exact rootVector_injective (hs.trans hr.symm)

set_option maxHeartbeats 10000000 in
-- Restrict the height-one check to the enumerated positive roots.
private theorem positive_height_one_iff_simple_core :
    ∀ r : EnumeratedPositiveRoot,
      height r.1 = 1 ↔
        ∃ i : Fin 8, rootVector r.1 = simpleRoot i := by
  decide

/-- A positive root has height one exactly when it is simple. -/
theorem positive_height_one_iff_simple
    (r : Root) (hr : IsPositive r) :
    height r = 1 ↔
      ∃ i : Fin 8, rootVector r = simpleRoot i :=
  positive_height_one_iff_simple_core
    ⟨r, by simpa [positiveRoots] using hr⟩

set_option maxHeartbeats 50000000 in
-- Search only the 120 positive roots for the lowered root.
private theorem positive_root_simple_subtraction_core :
    ∀ r : EnumeratedPositiveRoot,
      1 < height r.1 →
        ∃ i : Fin 8, ∃ s : EnumeratedPositiveRoot,
          rootVector s.1 =
              (fun k => rootVector r.1 k - simpleRoot i k) ∧
          height s.1 = height r.1 - 1 := by
  decide

/-- Every nonsimple positive root admits a simple-root subtraction that stays
positive and lowers height by one. -/
theorem positive_root_simple_subtraction
    (r : Root) (hr : IsPositive r) (hheight : 1 < height r) :
    ∃ i : Fin 8, ∃ s : Root,
      IsPositive s ∧
      rootVector s = (fun k => rootVector r k - simpleRoot i k) ∧
      height s = height r - 1 := by
  obtain ⟨i, s, hvec, hsheight⟩ :=
    positive_root_simple_subtraction_core
      ⟨r, by simpa [positiveRoots] using hr⟩ hheight
  exact
    ⟨i, s.1, enumeratedPositiveRoot_isPositive s, hvec, hsheight⟩

set_option maxHeartbeats 100000000 in
-- Shape closure checks no candidate witness roots.
private theorem positiveA2Pair_sum_isConcrete :
    ∀ p : ↥positiveA2PairFinset,
      IsConcreteRootVector (addRootVectors p.1.1 p.1.2) := by
  decide

set_option maxHeartbeats 100000000 in
-- Coefficient additivity is certified on precisely the positive A₂ pairs.
private theorem positiveA2Pair_sum_coefficients :
    ∀ p : ↥positiveA2PairFinset,
      coefficients (addRootVectors p.1.1 p.1.2) =
        fun i =>
          coefficients (rootVector p.1.1) i +
            coefficients (rootVector p.1.2) i := by
  decide

/-- Every positive `A₂` pair has a positive sum root, and height is additive
on that sum. -/
theorem positive_a2_pair_has_sum (p : PositiveA2Pair) :
    ∃ s : Root,
      IsPositive s ∧
      rootVector s = addRootVectors p.1.1 p.1.2 ∧
      height s = height p.1.1 + height p.1.2 := by
  let ep : ↥positiveA2PairFinset :=
    ⟨p.1, (positiveA2PairFinset_spec p.1).2 p.2⟩
  obtain ⟨s, hvec⟩ :=
    (isConcreteRootVector_iff (addRootVectors ep.1.1 ep.1.2)).mp
      (positiveA2Pair_sum_isConcrete ep)
  have hcoeff :
      coefficients (rootVector s) =
        fun i =>
          coefficients (rootVector p.1.1) i +
            coefficients (rootVector p.1.2) i := by
    rw [hvec]
    simpa [ep] using positiveA2Pair_sum_coefficients ep
  refine ⟨s, ?_, ?_, ?_⟩
  · intro i
    rw [hcoeff]
    exact add_nonneg (p.2.1 i) (p.2.2.1 i)
  · simpa [ep] using hvec
  · simp only [height, hcoeff, Finset.sum_add_distrib]

/-- A root with a prescribed concrete sum vector is unique. -/
theorem root_sum_unique (α β : Root) {γ δ : Root}
    (hγ : rootVector γ = addRootVectors α β)
    (hδ : rootVector δ = addRootVectors α β) :
    γ = δ :=
  rootVector_injective (hγ.trans hδ.symm)

end ConcreteRootSystem
end E8
end RiemannResearch
