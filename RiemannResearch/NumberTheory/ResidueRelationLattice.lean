/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# The integral relation lattice of a finite conductor dictionary

Source: user-provided squarefree profinite lattice research agenda,
16 October 2026, Target 5, for the integer relation lattice and its index.
The proof uses the coordinate of the full period and the first isomorphism
theorem for additive groups. The explicit integral basis uses the full-period
coordinate. Conversion to a prime-coordinate basis is a separate statement.

For a dictionary of divisors `d i` of `L`, the homomorphism is the integral
relation charge `sum_i (L / d i) * z i`, reduced modulo `L`. The proofs below
in fact need only that one dictionary coordinate equals the positive period.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.NumberTheory.ResidueRelationLattice

variable {ι : Type*} [Fintype ι]

/-- The integer reciprocal charge after clearing the common period. -/
def integerCharge (L : ℕ) (d : ι → ℕ) (z : ι → ℤ) : ℤ :=
  ∑ i, ((L / d i : ℕ) : ℤ) * z i

/-- The congruence homomorphism defining the full integer relation lattice. -/
def residueHom (L : ℕ) (d : ι → ℕ) : (ι → ℤ) →+ ZMod L where
  toFun z := (integerCharge L d z : ZMod L)
  map_zero' := by simp [integerCharge]
  map_add' z w := by
    simp [integerCharge, mul_add, Finset.sum_add_distrib]

/-- Integral relations modulo the common period, as an actual additive subgroup. -/
def relationLattice (L : ℕ) (d : ι → ℕ) : AddSubgroup (ι → ℤ) :=
  (residueHom L d).ker

theorem mem_relationLattice_iff (L : ℕ) (d : ι → ℕ) (z : ι → ℤ) :
    z ∈ relationLattice L d ↔ (integerCharge L d z : ZMod L) = 0 := by
  rfl

/-- Membership is precisely the cleared-denominator integer congruence. -/
theorem mem_relationLattice_iff_dvd (L : ℕ) (d : ι → ℕ) (z : ι → ℤ) :
    z ∈ relationLattice L d ↔ (L : ℤ) ∣ integerCharge L d z := by
  rw [mem_relationLattice_iff]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

/-- The full-period coordinate has unit weight, so every residue is attained. -/
theorem residueHom_surjective (L : ℕ) [NeZero L] (d : ι → ℕ)
    (i₀ : ι) (hi₀ : d i₀ = L) : Function.Surjective (residueHom L d) := by
  classical
  intro x
  refine ⟨fun i => if i = i₀ then (x.val : ℤ) else 0, ?_⟩
  change (integerCharge L d _ : ZMod L) = x
  have he : integerCharge L d
      (fun i => if i = i₀ then (x.val : ℤ) else 0) = (x.val : ℤ) := by
    unfold integerCharge
    rw [Finset.sum_eq_single i₀]
    · rw [hi₀, Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne L))]
      simp
    · intro i _ hi
      simp [hi]
    · simp
  rw [he]
  simp

/-- Exact quotient identification, stronger than merely counting the index. -/
def quotientEquiv (L : ℕ) [NeZero L] (d : ι → ℕ)
    (i₀ : ι) (hi₀ : d i₀ = L) :
    ((ι → ℤ) ⧸ relationLattice L d) ≃+ ZMod L :=
  QuotientAddGroup.quotientKerEquivOfSurjective (residueHom L d)
    (residueHom_surjective L d i₀ hi₀)

/-- The integer relation lattice has index exactly the positive common period. -/
theorem index_eq (L : ℕ) [NeZero L] (d : ι → ℕ)
    (i₀ : ι) (hi₀ : d i₀ = L) : (relationLattice L d).index = L := by
  rw [AddSubgroup.index_eq_card]
  calc
    Nat.card ((ι → ℤ) ⧸ relationLattice L d) = Nat.card (ZMod L) :=
      Nat.card_congr (quotientEquiv L d i₀ hi₀).toEquiv
    _ = L := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- The requested finite-set formulation: the dictionary contains its period. -/
theorem finset_relation_index (D : Finset ℕ) (L : ℕ)
    (hL : 0 < L) (hmem : L ∈ D) :
    (relationLattice L (fun d : D => d.val)).index = L := by
  let : NeZero L := ⟨ne_of_gt hL⟩
  exact index_eq L (fun d : D => d.val) ⟨L, hmem⟩ rfl

end RiemannResearch.NumberTheory.ResidueRelationLattice

noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.ResidueRelationLattice
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateVector (i : ι) : ι → ℤ := fun j => if j = i then 1 else 0

/-- The non-distinguished basis vector is `e_i - (L/d_i)e_i₀`. -/
def relationGenerator (L : ℕ) (d : ι → ℕ) (i₀ i : ι) : ι → ℤ :=
  fun j => coordinateVector i j - ((L / d i : ℕ) : ℤ) * coordinateVector i₀ j

/-- Coordinates for `k L e_i₀ + sum_i a_i (e_i - (L/d_i)e_i₀)`.
For unique coordinates one imposes `a i₀ = 0`. -/
def basisCombination (L : ℕ) (d : ι → ℕ) (i₀ : ι) (k : ℤ) (a : ι → ℤ) : ι → ℤ :=
  fun j => a j + if j = i₀ then (L : ℤ) * k - integerCharge L d a else 0

theorem basisCombination_eq_generators (L : ℕ) (d : ι → ℕ)
    (i₀ : ι) (k : ℤ) (a : ι → ℤ) :
    basisCombination L d i₀ k a = fun j =>
      k * (L : ℤ) * coordinateVector i₀ j + ∑ i, a i * relationGenerator L d i₀ i j := by
  funext j
  have hs : (∑ i, a i * relationGenerator L d i₀ i j) =
      a j - integerCharge L d a * coordinateVector i₀ j := by
    simp only [relationGenerator, mul_sub, Finset.sum_sub_distrib]
    have hfirst : (∑ i, a i * coordinateVector i j) = a j := by
      simp [coordinateVector, mul_ite]
    rw [hfirst]
    congr 1
    simp only [integerCharge, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  by_cases hj : j = i₀ <;> simp [basisCombination, coordinateVector, hj] <;> ring

theorem integerCharge_add_single (L : ℕ) [NeZero L] (d : ι → ℕ)
    (i₀ : ι) (hi₀ : d i₀ = L) (a : ι → ℤ) (t : ℤ) :
    integerCharge L d (fun j => a j + if j = i₀ then t else 0) = integerCharge L d a + t := by
  have hw : ((L / d i₀ : ℕ) : ℤ) = 1 := by
    rw [hi₀, Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne L))]
    rfl
  unfold integerCharge
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i₀]
  · simp only [ite_true, hw, one_mul]
  · intro i _ hi
    simp [hi]
  · simp

theorem basisCombination_mem (L : ℕ) [NeZero L] (d : ι → ℕ)
    (i₀ : ι) (hi₀ : d i₀ = L) (k : ℤ) (a : ι → ℤ) :
    basisCombination L d i₀ k a ∈ relationLattice L d := by
  rw [mem_relationLattice_iff_dvd]
  refine ⟨k, ?_⟩
  change integerCharge L d
    (fun j => a j + if j = i₀ then (L : ℤ) * k - integerCharge L d a else 0) = _
  rw [integerCharge_add_single L d i₀ hi₀]
  ring

/-- Every integral relation has an expansion in the displayed basis with the
redundant distinguished coefficient zero. -/
theorem exists_basisCombination (L : ℕ) [NeZero L] (d : ι → ℕ)
    (i₀ : ι) (hi₀ : d i₀ = L) (z : ι → ℤ) (hz : z ∈ relationLattice L d) :
    ∃ k : ℤ, ∃ a : ι → ℤ, a i₀ = 0 ∧ basisCombination L d i₀ k a = z := by
  rcases (mem_relationLattice_iff_dvd L d z).mp hz with ⟨k, hk⟩
  let a : ι → ℤ := fun j => z j + if j = i₀ then -z i₀ else 0
  have ha : a i₀ = 0 := by simp [a]
  have hc : integerCharge L d a = integerCharge L d z - z i₀ := by
    change integerCharge L d (fun j => z j + if j = i₀ then -z i₀ else 0) = _
    rw [integerCharge_add_single L d i₀ hi₀]
    ring
  refine ⟨k, a, ha, ?_⟩
  funext j
  by_cases hj : j = i₀
  · subst j
    simp only [basisCombination, ite_true, ha, zero_add, hc, hk]
    ring
  · simp [basisCombination, hj, a]

/-- The coefficients in the basis expansion are unique. -/
theorem basisCombination_injective (L : ℕ) [NeZero L] (d : ι → ℕ) (i₀ : ι)
    (k l : ℤ) (a b : ι → ℤ) (ha : a i₀ = 0) (hb : b i₀ = 0)
    (h : basisCombination L d i₀ k a = basisCombination L d i₀ l b) : k = l ∧ a = b := by
  have hab : a = b := by
    funext j
    by_cases hj : j = i₀
    · simp [hj, ha, hb]
    · simpa [basisCombination, hj] using congrFun h j
  subst b
  have hh := congrFun h i₀
  simp only [basisCombination, ite_true, ha, zero_add] at hh
  have hm : (L : ℤ) * k = (L : ℤ) * l := sub_left_inj.mp hh
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  exact ⟨mul_left_cancel₀ hL hm, rfl⟩

end RiemannResearch.NumberTheory.ResidueRelationLattice
