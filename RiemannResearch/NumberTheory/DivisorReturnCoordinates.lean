import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Exact divisor returns and a parity obstruction to Haar pseudorandomness

Source: Christian Noack, `sdf_modified.pdf`, sections 14.9 and 14.14,
especially Hypothesis 14.9. Divisor return coordinates need no
squarefreeness. When the reduced modulus is even, the nontrivial parity
character has average -1 on every nonempty return sample, while its Haar
average is zero. Thus an all-character comparison to Haar cannot have
error tending to zero. This does not rule out a comparison to the unit
measure, or estimates for particular centered observables.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.DivisorReturnCoordinates

theorem gcd_mul_eq_divisor_iff (d Q m : ℕ) (hd : 0 < d) :
    Nat.gcd (d * m) (d * Q) = d ↔ Nat.Coprime m Q := by
  rw [Nat.gcd_mul_left]
  change d * Nat.gcd m Q = d ↔ Nat.gcd m Q = 1
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_left hd (by simpa using h)
  · intro h
    simp [h]

theorem return_coordinates (d Q n : ℕ) (hd : 0 < d) :
    Nat.gcd n (d * Q) = d ↔ ∃ m, n = d * m ∧ Nat.Coprime m Q := by
  constructor
  · intro h
    have hdn : d ∣ n := h ▸ Nat.gcd_dvd_left n (d * Q)
    obtain ⟨m,hm⟩ := hdn
    exact ⟨m,hm,(gcd_mul_eq_divisor_iff d Q m hd).mp (hm ▸ h)⟩
  · rintro ⟨m,rfl,hm⟩
    exact (gcd_mul_eq_divisor_iff d Q m hd).mpr hm

def parityCharacter (n : ℕ) : ℝ := (-1) ^ n

theorem parityCharacter_coprime_even (Q n : ℕ)
    (hQ : 2 ∣ Q) (hn : Nat.Coprime n Q) : parityCharacter n = -1 := by
  have ho : Odd n := (hn.of_dvd_right hQ).odd_of_right
  exact ho.neg_one_pow

theorem parity_haar_sum (Q : ℕ) :
    (∑ n ∈ Finset.range (2 * Q), parityCharacter n) = 0 := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Nat.mul_succ]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp [parityCharacter, pow_add, pow_mul]

theorem parity_return_sum (Q : ℕ) (s : Finset ℕ) (hQ : 2 ∣ Q)
    (hs : ∀ n ∈ s, Nat.Coprime n Q) :
    (∑ n ∈ s, parityCharacter n) = -(s.card : ℝ) := by
  calc
    _ = ∑ _n ∈ s, (-1 : ℝ) := Finset.sum_congr rfl
      (fun n hn => parityCharacter_coprime_even Q n hQ (hs n hn))
    _ = _ := by simp

/-- The normalized return character bias is exactly one, for every nonempty sample. -/
theorem parity_return_bias (Q : ℕ) (s : Finset ℕ) (hQ : 2 ∣ Q)
    (hs : ∀ n ∈ s, Nat.Coprime n Q) (hne : s.Nonempty) :
    |(∑ n ∈ s, parityCharacter n) / s.card| = 1 := by
  rw [parity_return_sum Q s hQ hs]
  have hc : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hne)
  simp [hc]

theorem no_subunit_haar_character_bound (Q : ℕ) (s : Finset ℕ)
    (hQ : 2 ∣ Q) (hs : ∀ n ∈ s, Nat.Coprime n Q) (hne : s.Nonempty)
    (ε : ℝ) (hε : ε < 1) :
    ¬ |(∑ n ∈ s, parityCharacter n) / s.card| ≤ ε := by
  rw [parity_return_bias Q s hQ hs hne]
  exact not_le.mpr hε

end RiemannResearch.NumberTheory.DivisorReturnCoordinates
