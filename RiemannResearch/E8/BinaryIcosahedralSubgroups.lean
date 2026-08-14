/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.E8.BinaryIcosahedralFinite
import RiemannResearch.GaloisCohomology.TwoGaugeDoubleCoset
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The binary-icosahedral subgroup diamond in SL(2, F5)

This promotes the finite carriers in BinaryIcosahedralFinite to actual
subgroups. It transports the group structure of SpecialLinearGroup to the
determinant-one tuple model, checks closure on the computable carriers, and
maps the resulting subgroups back into SL(2, ZMod 5).

The order-24 and order-20 subgroups have order-4 intersection, generate the
order-120 group, and have indices 5 and 6. The last theorem specializes
admissible two-gauge descent to this fixed subgroup diamond. It does not
construct E8-valued gauges, oriented torus data, or constrained factorization.
-/

open Matrix

namespace RiemannResearch.E8.BinaryIcosahedralSubgroups

open RiemannResearch.E8.BinaryIcosahedralFinite
open RiemannResearch.GaloisCohomology

abbrev Z5 := ZMod 5
abbrev SL2F5 := Matrix.SpecialLinearGroup (Fin 2) Z5
abbrev TupleSL2 :=
  {x : M // RiemannResearch.E8.BinaryIcosahedralFinite.det x = 1}

def tupleMatrix (x : M) : Matrix (Fin 2) (Fin 2) Z5 :=
  !![ZMod.finEquiv 5 (a x), ZMod.finEquiv 5 (b x);
     ZMod.finEquiv 5 (c x), ZMod.finEquiv 5 (d x)]

def toSL2 (x : TupleSL2) : SL2F5 := by
  refine ⟨tupleMatrix x.1, ?_⟩
  rw [tupleMatrix, Matrix.det_fin_two_of]
  have hx := congrArg (fun z : F5 => ZMod.finEquiv 5 z) x.2
  simpa only [map_sub, map_mul, map_one,
    RiemannResearch.E8.BinaryIcosahedralFinite.det] using hx

def fromSL2 (x : SL2F5) : TupleSL2 := by
  let e := ZMod.finEquiv 5
  refine ⟨mat (e.symm (x.1 0 0)) (e.symm (x.1 0 1))
    (e.symm (x.1 1 0)) (e.symm (x.1 1 1)), ?_⟩
  have hx := congrArg (fun z : Z5 => e.symm z) x.det_coe
  rw [Matrix.det_fin_two] at hx
  simpa only [map_sub, map_mul, map_one,
    RiemannResearch.E8.BinaryIcosahedralFinite.det, mat, a, b, c, d] using hx

def tupleSL2Equiv : TupleSL2 ≃ SL2F5 where
  toFun := toSL2
  invFun := fromSL2
  left_inv := by
    intro x
    apply Subtype.ext
    rcases x with ⟨⟨aa, bb, cc, dd⟩, hx⟩
    simp [toSL2, fromSL2, tupleMatrix, mat, a, b, c, d]
  right_inv := by
    intro x
    apply Subtype.ext
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [toSL2, fromSL2, tupleMatrix, mat, a, b, c, d]

instance : Group TupleSL2 := tupleSL2Equiv.group

def tupleSL2MulEquiv : TupleSL2 ≃* SL2F5 where
  toEquiv := tupleSL2Equiv
  map_mul' := by
    intro x y
    change tupleSL2Equiv
        (tupleSL2Equiv.symm (tupleSL2Equiv x * tupleSL2Equiv y)) =
      tupleSL2Equiv x * tupleSL2Equiv y
    exact tupleSL2Equiv.apply_symm_apply _

def liftFinset (s : Finset M) : Finset TupleSL2 :=
  Finset.univ.filter (fun x => x.1 ∈ s)

def q8Carrier : Finset TupleSL2 := liftFinset q8
def binaryTetrahedralCarrier : Finset TupleSL2 :=
  liftFinset binaryTetrahedral
def binaryDihedralCarrier : Finset TupleSL2 := liftFinset binaryDihedral
def overlapCarrier : Finset TupleSL2 := liftFinset c4

set_option maxHeartbeats 0 in
-- Exhaustive kernel reduction over the 120-element tuple model.
set_option maxRecDepth 100000 in
theorem lifted_cards :
    Fintype.card TupleSL2 = 120 ∧ q8Carrier.card = 8 ∧
    binaryTetrahedralCarrier.card = 24 ∧
    binaryDihedralCarrier.card = 20 ∧ overlapCarrier.card = 4 := by
  decide

def subgroupOfFinset (s : Finset TupleSL2) (hone : 1 ∈ s)
    (hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ s)
    (hinv : ∀ x ∈ s, x⁻¹ ∈ s) : Subgroup TupleSL2 where
  carrier := {x | x ∈ s}
  one_mem' := hone
  mul_mem' := fun hx hy => hmul _ hx _ hy
  inv_mem' := fun hx => hinv _ hx

theorem subgroupOfFinset_card (s : Finset TupleSL2) (hone hmul hinv) :
    Nat.card (subgroupOfFinset s hone hmul hinv) = s.card := by
  let _ : Fintype (subgroupOfFinset s hone hmul hinv) :=
    Fintype.ofFinset s (by intro x; rfl)
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_ofFinset s (by intro x; rfl)

set_option maxHeartbeats 0 in
-- Exhaustive kernel reduction verifies the finite carrier closure.
set_option maxRecDepth 100000 in
def tupleQ8 : Subgroup TupleSL2 :=
  subgroupOfFinset q8Carrier (by decide) (by decide) (by decide)

set_option maxHeartbeats 0 in
-- Exhaustive kernel reduction verifies the finite carrier closure.
set_option maxRecDepth 100000 in
def tupleBinaryTetrahedral : Subgroup TupleSL2 :=
  subgroupOfFinset binaryTetrahedralCarrier
    (by decide) (by decide) (by decide)

set_option maxHeartbeats 0 in
-- Exhaustive kernel reduction verifies the finite carrier closure.
set_option maxRecDepth 100000 in
def tupleBinaryDihedral : Subgroup TupleSL2 :=
  subgroupOfFinset binaryDihedralCarrier
    (by decide) (by decide) (by decide)

set_option maxHeartbeats 0 in
-- Exhaustive kernel reduction verifies the finite carrier closure.
set_option maxRecDepth 100000 in
def tupleOverlap : Subgroup TupleSL2 :=
  subgroupOfFinset overlapCarrier (by decide) (by decide) (by decide)

theorem tupleSL2_card : Nat.card TupleSL2 = 120 := by
  rw [Nat.card_eq_fintype_card]
  exact lifted_cards.1

theorem tupleQ8_card : Nat.card tupleQ8 = 8 := by
  rw [tupleQ8, subgroupOfFinset_card]
  exact lifted_cards.2.1

theorem tupleBinaryTetrahedral_card :
    Nat.card tupleBinaryTetrahedral = 24 := by
  rw [tupleBinaryTetrahedral, subgroupOfFinset_card]
  exact lifted_cards.2.2.1

theorem tupleBinaryDihedral_card :
    Nat.card tupleBinaryDihedral = 20 := by
  rw [tupleBinaryDihedral, subgroupOfFinset_card]
  exact lifted_cards.2.2.2.1

theorem tupleOverlap_card : Nat.card tupleOverlap = 4 := by
  rw [tupleOverlap, subgroupOfFinset_card]
  exact lifted_cards.2.2.2.2

set_option maxHeartbeats 0 in
-- Exhaustive kernel reduction identifies the finite subgroup intersection.
set_option maxRecDepth 100000 in
theorem tuple_inf_eq :
    tupleBinaryTetrahedral ⊓ tupleBinaryDihedral = tupleOverlap := by
  have hsets :
      binaryTetrahedralCarrier ∩ binaryDihedralCarrier =
        overlapCarrier := by
    decide
  ext x
  change (x ∈ binaryTetrahedralCarrier ∧
      x ∈ binaryDihedralCarrier) ↔ x ∈ overlapCarrier
  rw [← Finset.mem_inter, hsets]

def tupleProductSet : Finset TupleSL2 :=
  (binaryTetrahedralCarrier.product binaryDihedralCarrier).image
    (fun p => p.1 * p.2)

set_option maxHeartbeats 0 in
-- Exhaustive kernel reduction verifies that every group element is a product.
set_option maxRecDepth 100000 in
theorem tupleProductSet_eq_univ : tupleProductSet = Finset.univ := by
  decide

theorem tuple_sup_eq :
    tupleBinaryTetrahedral ⊔ tupleBinaryDihedral = ⊤ := by
  apply top_unique
  intro x hx
  have hxp : x ∈ tupleProductSet := by
    rw [tupleProductSet_eq_univ]
    simp
  obtain ⟨p, hp, hpval⟩ := Finset.mem_image.mp hxp
  obtain ⟨hpH, hpK⟩ := Finset.mem_product.mp hp
  rw [← hpval]
  have hpH' :
      p.1 ∈ tupleBinaryTetrahedral ⊔ tupleBinaryDihedral :=
    (show tupleBinaryTetrahedral ≤
      tupleBinaryTetrahedral ⊔ tupleBinaryDihedral from le_sup_left) hpH
  have hpK' :
      p.2 ∈ tupleBinaryTetrahedral ⊔ tupleBinaryDihedral :=
    (show tupleBinaryDihedral ≤
      tupleBinaryTetrahedral ⊔ tupleBinaryDihedral from le_sup_right) hpK
  exact
    (tupleBinaryTetrahedral ⊔ tupleBinaryDihedral).mul_mem hpH' hpK'

def q8Subgroup : Subgroup SL2F5 :=
  tupleQ8.map tupleSL2MulEquiv.toMonoidHom
def binaryTetrahedralSubgroup : Subgroup SL2F5 :=
  tupleBinaryTetrahedral.map tupleSL2MulEquiv.toMonoidHom
def binaryDihedralSubgroup : Subgroup SL2F5 :=
  tupleBinaryDihedral.map tupleSL2MulEquiv.toMonoidHom
def overlapSubgroup : Subgroup SL2F5 :=
  tupleOverlap.map tupleSL2MulEquiv.toMonoidHom

theorem sl2F5_card : Nat.card SL2F5 = 120 :=
  (Nat.card_congr tupleSL2MulEquiv.toEquiv).symm.trans tupleSL2_card

theorem q8Subgroup_card : Nat.card q8Subgroup = 8 :=
  (Nat.card_congr
    (tupleSL2MulEquiv.subgroupMap tupleQ8).toEquiv).symm.trans
      tupleQ8_card

theorem binaryTetrahedralSubgroup_card :
    Nat.card binaryTetrahedralSubgroup = 24 :=
  (Nat.card_congr
    (tupleSL2MulEquiv.subgroupMap tupleBinaryTetrahedral).toEquiv).symm.trans
      tupleBinaryTetrahedral_card

theorem binaryDihedralSubgroup_card :
    Nat.card binaryDihedralSubgroup = 20 :=
  (Nat.card_congr
    (tupleSL2MulEquiv.subgroupMap tupleBinaryDihedral).toEquiv).symm.trans
      tupleBinaryDihedral_card

theorem overlapSubgroup_card : Nat.card overlapSubgroup = 4 :=
  (Nat.card_congr
    (tupleSL2MulEquiv.subgroupMap tupleOverlap).toEquiv).symm.trans
      tupleOverlap_card

theorem binarySubgroup_inf :
    binaryTetrahedralSubgroup ⊓ binaryDihedralSubgroup =
      overlapSubgroup := by
  change
    Subgroup.map tupleSL2MulEquiv.toMonoidHom tupleBinaryTetrahedral ⊓
      Subgroup.map tupleSL2MulEquiv.toMonoidHom tupleBinaryDihedral =
    Subgroup.map tupleSL2MulEquiv.toMonoidHom tupleOverlap
  rw [← Subgroup.map_inf tupleBinaryTetrahedral tupleBinaryDihedral
    tupleSL2MulEquiv.toMonoidHom tupleSL2MulEquiv.injective, tuple_inf_eq]

theorem binarySubgroup_sup :
    binaryTetrahedralSubgroup ⊔ binaryDihedralSubgroup = ⊤ := by
  change
    Subgroup.map tupleSL2MulEquiv.toMonoidHom tupleBinaryTetrahedral ⊔
      Subgroup.map tupleSL2MulEquiv.toMonoidHom tupleBinaryDihedral = ⊤
  rw [← Subgroup.map_sup, tuple_sup_eq]
  apply top_unique
  intro y hy
  obtain ⟨x, rfl⟩ := tupleSL2MulEquiv.surjective y
  exact ⟨x, Subgroup.mem_top x, rfl⟩

theorem binaryTetrahedralSubgroup_index :
    binaryTetrahedralSubgroup.index = 5 := by
  have hcard := binaryTetrahedralSubgroup.card_mul_index
  rw [binaryTetrahedralSubgroup_card, sl2F5_card] at hcard
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 24)
  norm_num at hcard ⊢
  exact hcard

theorem binaryDihedralSubgroup_index :
    binaryDihedralSubgroup.index = 6 := by
  have hcard := binaryDihedralSubgroup.card_mul_index
  rw [binaryDihedralSubgroup_card, sl2F5_card] at hcard
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 20)
  norm_num at hcard ⊢
  exact hcard

theorem binaryIcosahedral_subgroup_lattice :
    Nat.card SL2F5 = 120 ∧ Nat.card q8Subgroup = 8 ∧
    Nat.card binaryTetrahedralSubgroup = 24 ∧
    Nat.card binaryDihedralSubgroup = 20 ∧
    Nat.card overlapSubgroup = 4 ∧
    binaryTetrahedralSubgroup ⊓ binaryDihedralSubgroup =
      overlapSubgroup ∧
    binaryTetrahedralSubgroup ⊔ binaryDihedralSubgroup = ⊤ ∧
    binaryTetrahedralSubgroup.index = 5 ∧
    binaryDihedralSubgroup.index = 6 :=
  ⟨sl2F5_card, q8Subgroup_card, binaryTetrahedralSubgroup_card,
    binaryDihedralSubgroup_card, overlapSubgroup_card, binarySubgroup_inf,
    binarySubgroup_sup, binaryTetrahedralSubgroup_index,
    binaryDihedralSubgroup_index⟩

universe u

theorem
    isCoboundary_of_binaryIcosahedral_admissible_orientedTransition_factorization
    {G : Type u} [Group G] [MulDistribMulAction SL2F5 G]
    (a : NonabelianCocycle SL2F5 G) (gH gK : G)
    (hH : ∀ σ : binaryTetrahedralSubgroup,
      a σ.1 = gH⁻¹ * σ.1 • gH)
    (hK : ∀ σ : binaryDihedralSubgroup,
      a σ.1 = gK⁻¹ * σ.1 • gK)
    (S6 S5 : Subgroup G) (theta : S6 ≃* S5)
    (htransport :
      gH * gK⁻¹ ∈ orientedSubgroupTransporter S6 S5 theta)
    (hfactor :
      ∀ x : G,
        IsAdmissibleTwoGaugeTransition
          binaryTetrahedralSubgroup binaryDihedralSubgroup x →
        x ∈ orientedSubgroupTransporter S6 S5 theta →
        ∃ u v : G,
          NonabelianCocycle.IsFixedBy binaryTetrahedralSubgroup u ∧
          NonabelianCocycle.IsFixedBy binaryDihedralSubgroup v ∧ x = u * v) :
    a.IsCoboundary :=
  isCoboundary_of_admissible_orientedTransition_factorization
    a binaryTetrahedralSubgroup binaryDihedralSubgroup binarySubgroup_sup
    gH gK hH hK S6 S5 theta htransport hfactor

end RiemannResearch.E8.BinaryIcosahedralSubgroups
