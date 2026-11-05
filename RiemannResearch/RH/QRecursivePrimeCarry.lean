/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QMixedRadixCarry
import Mathlib.Algebra.BigOperators.Intervals

/-! # Telescoping the integer carries along a finite CRT factor chain

Source: user-proposed iteration of the fractional-part formula. Each internal
floor is kept with its exact integer multiplier. A single outer fractional
part removes the resulting integer. Nothing in this algebra requires passing
to an infinite limit. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CRTCarryArithmetic
open ArithmeticCumulative

/-- Affine recurrence shared by the raw residue argument and its integer carries. -/
def carryFold {R : Type*} [Semiring R] (u : R) (a z : ℕ → R) : ℕ → R
  | 0 => u
  | k + 1 => a k * carryFold u a z k + z k

/-- Each local term is multiplied by every subsequent multiplier on the path. -/
theorem carryFold_eq_sum {R : Type*} [CommSemiring R] (u : R) (a z : ℕ → R) (k : ℕ) :
    carryFold u a z k = (∏ i ∈ Finset.range k, a i) * u +
      ∑ i ∈ Finset.range k, (∏ j ∈ Finset.Ico (i + 1) k, a j) * z i := by
  induction k with
  | zero => simp [carryFold]
  | succ k ih =>
    rw [carryFold, ih, Finset.prod_range_succ, Finset.sum_range_succ]
    simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
    have he : (∑ i ∈ Finset.range k, (∏ j ∈ Finset.Ico (i + 1) (k + 1), a j) * z i) =
        a k * ∑ i ∈ Finset.range k, (∏ j ∈ Finset.Ico (i + 1) k, a j) * z i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.prod_Ico_succ_top (Finset.mem_range.mp hi) a]
      ring
    rw [he]
    ring

/-- The actual terminal modulus after adjoining the first k factors. -/
def carryConductor (d : ℕ) (p : ℕ → ℕ) (k : ℕ) : ℕ :=
  d * ∏ i ∈ Finset.range k, p i

private theorem carryConductor_succ (d : ℕ) (p : ℕ → ℕ) (k : ℕ) :
    carryConductor d p (k + 1) = carryConductor d p k * p k := by
  simp [carryConductor, Finset.prod_range_succ, Nat.mul_assoc]

private theorem carryConductor_pos (d : ℕ) (p : ℕ → ℕ) (k : ℕ) (hd : 0 < d)
    (hp : ∀ i < k, 0 < p i) : 0 < carryConductor d p k :=
  Nat.mul_pos hd (Finset.prod_pos (fun i hi => hp i (Finset.mem_range.mp hi)))

/-- The total raw argument equals the terminal residue plus the sum of all
transported floor carries. Only the certificates on the chosen path are needed. -/
theorem recursivePrimeCarry_exact (d : ℕ) (p : ℕ → ℕ) (a b t : ℕ → ℤ) (n k : ℕ)
    (hd : 0 < d) (hp : ∀ i < k, 0 < p i)
    (hc : ∀ i < k, (a i : ℝ) * (p i : ℝ) + (b i : ℝ) * (carryConductor d p i : ℝ) =
      1 + (t i : ℝ) * (carryConductor d p i : ℝ) * (p i : ℝ)) :
    carryFold (residueFraction d n) (fun i => (a i : ℝ))
        (fun i => (b i : ℝ) * residueFraction (p i) n) k =
      residueFraction (carryConductor d p k) n +
        ((carryFold (0 : ℤ) a (fun i => carry (carryConductor d p i) (p i) (a i) (b i) n) k : ℤ) : ℝ) := by
  induction k with
  | zero => simp [carryFold, carryConductor]
  | succ k ih =>
    have hp' : ∀ i < k, 0 < p i := fun i hi => hp i (Nat.lt_succ_of_lt hi)
    have hprev := ih hp' (fun i hi => hc i (Nat.lt_succ_of_lt hi))
    have hsite := real_decomposition (carryConductor d p k) (p k) (a k) (b k) (t k) n
      (carryConductor_pos d p k hd hp') (hp k (Nat.lt_succ_self k)) (hc k (Nat.lt_succ_self k))
    rw [carryFold, carryFold, hprev, carryConductor_succ, Int.cast_add, Int.cast_mul]
    linear_combination -hsite

/-- Taking one fractional part gives the terminal atom; taking one floor gives
the exact integer accumulated along the path. -/
theorem recursivePrimeCarry_fract_floor (d : ℕ) (p : ℕ → ℕ) (a b t : ℕ → ℤ) (n k : ℕ)
    (hd : 0 < d) (hp : ∀ i < k, 0 < p i)
    (hc : ∀ i < k, (a i : ℝ) * (p i : ℝ) + (b i : ℝ) * (carryConductor d p i : ℝ) =
      1 + (t i : ℝ) * (carryConductor d p i : ℝ) * (p i : ℝ)) :
    let x := carryFold (residueFraction d n) (fun i => (a i : ℝ))
      (fun i => (b i : ℝ) * residueFraction (p i) n) k
    Int.fract x = residueFraction (carryConductor d p k) n ∧
      ⌊x⌋ = carryFold (0 : ℤ) a (fun i => carry (carryConductor d p i) (p i) (a i) (b i) n) k := by
  dsimp only
  have hz : ⌊residueFraction (carryConductor d p k) n⌋ = 0 :=
    Int.floor_eq_zero_iff.mpr ⟨residueFraction_nonneg _ _,
      residueFraction_lt_one _ _ (carryConductor_pos d p k hd hp)⟩
  rw [recursivePrimeCarry_exact d p a b t n k hd hp hc, Int.fract_add_intCast,
    Int.floor_add_intCast, hz, zero_add]
  simp [Int.fract, hz]

/-- An integer multiplier lets each successive fractional part be flattened. -/
theorem fract_affine_previous (x y : ℝ) (a : ℤ) :
    Int.fract ((a : ℝ) * Int.fract x + y) = Int.fract ((a : ℝ) * x + y) := by
  apply Int.fract_eq_fract.mpr
  refine ⟨-(a * ⌊x⌋), ?_⟩
  rw [Int.fract, Int.cast_neg, Int.cast_mul]
  ring

end RiemannResearch.RH.CRTCarryArithmetic
