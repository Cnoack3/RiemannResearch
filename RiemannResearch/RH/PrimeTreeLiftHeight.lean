/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeLifts
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # One prime coordinate prescribes the CRT height

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros*, 5 November
2026, §2.1. The same signed integer occurs in the raw argument and the floor.
The change works at every site and leaves the composite fractional part fixed.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimeCRTCarries
open ArithmeticCumulative

/-- Shift exactly one prime representative by an integral multiple of its prime. -/
def shiftPrimeLift (c : ℕ → ℝ) (p : ℕ) (t : ℤ) (q : ℕ) : ℝ :=
  c q + if q = p then (p : ℝ) * t else 0

/-- Exact change in the height, in the physical raw sum, and in its integer carry. -/
theorem shiftPrimeLift_exact (d p : ℕ) (hp : p ∈ d.primeFactors) (c : ℕ → ℝ) (t : ℤ) :
    (∑ q ∈ d.primeFactors, shiftPrimeLift c p t q / q) = (∑ q ∈ d.primeFactors, c q / q) + t ∧
      ∀ n : ℕ,
        let x := ∑ q ∈ d.primeFactors, c q * residueFraction q n
        let y := ∑ q ∈ d.primeFactors, shiftPrimeLift c p t q * residueFraction q n
        y = x + ((t * (n % p : ℕ) : ℤ) : ℝ) ∧ Int.fract y = Int.fract x ∧ ⌊y⌋ = ⌊x⌋ + t * (n % p : ℕ) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero
  constructor
  · simp only [shiftPrimeLift, add_div, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single p]
    · simp [hpR, mul_div_cancel_left₀]
    · intro q _ hqp
      simp [hqp]
    · exact fun h => (h hp).elim
  · intro n
    dsimp only
    have hs : (∑ q ∈ d.primeFactors, shiftPrimeLift c p t q * residueFraction q n) =
        (∑ q ∈ d.primeFactors, c q * residueFraction q n) + ((t * (n % p : ℕ) : ℤ) : ℝ) := by
      simp only [shiftPrimeLift, add_mul, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single p]
      · simp only [if_pos rfl, residueFraction, Int.cast_mul, Int.cast_natCast]
        field_simp [hpR] <;> ring_nf <;> simp
      · intro q _ hqp
        simp [hqp]
      · exact fun h => (h hp).elim
    exact ⟨hs, by rw [hs, Int.fract_add_intCast], by rw [hs, Int.floor_add_intCast]⟩

/-- Starting at any admissible real lift and choosing any one prime coordinate,
we can realize a prescribed integer height without changing the physical atom. -/
theorem exists_single_prime_lift_height (d p : ℕ) (hd : 1 < d) (hsf : Squarefree d)
    (hp : p ∈ d.primeFactors) (c : ℕ → ℝ)
    (hc : ∀ q ∈ d.primeFactors, ∃ t : ℤ, c q = (canonicalCoefficient d q : ℝ) + (q : ℝ)*t)
    (target : ℤ) : ∃ t : ℤ,
      ((∑ q ∈ d.primeFactors, shiftPrimeLift c p t q / q) - 1 / (d : ℝ)) = (target : ℝ) ∧
      (∀ q, q ≠ p → shiftPrimeLift c p t q = c q) ∧
      (∀ n : ℕ, 0 < n → Int.fract (∑ q ∈ d.primeFactors,
        shiftPrimeLift c p t q * residueFraction q n) = residueFraction d n) := by
  obtain ⟨z, hz⟩ := prime_lift_height_integral d hd hsf c hc
  refine ⟨target - z, ?_, ?_, ?_⟩
  · rw [(shiftPrimeLift_exact d p hp c (target-z)).1, Int.cast_sub]
    linarith only [hz]
  · intro q hqp
    simp [shiftPrimeLift, hqp]
  · intro n hn
    exact ((shiftPrimeLift_exact d p hp c (target-z)).2 n).2.1.trans
      ((real_prime_lift_iff d (by omega) hsf c).mpr hc n hn)

end RiemannResearch.RH.QPrimeCRTCarries
