/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QGcdCellObstruction
import RiemannResearch.NumberTheory.VonMangoldtLCM
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# The refinement obstruction at genuine powers-of-two LCM admissions

Source: CanonicalPrimePowerUpdatesResearch20261107, Section 5.
The old cutoff is exactly lcm(1,...,2^k-1), not an arbitrary period.
Mathlib's exact prime valuation of lcmUpto supplies its odd complement.
-/

noncomputable section
namespace RiemannResearch.RH.QGcdCellLCMObstruction
open ZetaTwoHilbert QCRTFiniteCollocation QGcdCellObstruction

def lcmOddPart (k : ℕ) : ℕ := ordCompl[2] (Nat.lcmUpto (2 ^ k - 1))

theorem factorization_before_two_pow (k : ℕ) (hk : 2 ≤ k) :
    (Nat.lcmUpto (2 ^ k - 1)).factorization 2 = k - 1 := by
  rw [Nat.factorization_lcmUpto _ Nat.prime_two]
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hpos : 0 < 2 ^ (k - 1) := by positivity
    omega
  · rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hp : 0 < 2 ^ k := by positivity
    omega

theorem lcm_before_two_pow_decomposition (k : ℕ) (hk : 2 ≤ k) :
    2 ^ (k - 1) * lcmOddPart k = Nat.lcmUpto (2 ^ k - 1) := by
  have h := Nat.ordProj_mul_ordCompl_eq_self (Nat.lcmUpto (2 ^ k - 1)) 2
  simpa only [lcmOddPart, factorization_before_two_pow k hk] using h

theorem lcmOddPart_coprime_two (k : ℕ) : Nat.Coprime 2 (lcmOddPart k) :=
  Nat.coprime_ordCompl Nat.prime_two (Nat.lcmUpto_ne_zero _)

theorem lcmOddPart_pos (k : ℕ) : 0 < lcmOddPart k :=
  Nat.ordCompl_pos 2 (Nat.lcmUpto_ne_zero _)

theorem lcmOddPart_ge_three (k : ℕ) (hk : 2 ≤ k) : 3 ≤ lcmOddPart k := by
  have hpow : 4 ≤ 2 ^ k := by
    have h := Nat.pow_le_pow_right (by omega : 0 < 2) hk
    norm_num at h ⊢
    exact h
  have h3L : 3 ∣ Nat.lcmUpto (2 ^ k - 1) := by
    unfold Nat.lcmUpto
    exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hcop : Nat.Coprime 3 (2 ^ (k - 1)) :=
    (by norm_num : Nat.Coprime 3 2).pow_right _
  rw [← lcm_before_two_pow_decomposition k hk] at h3L
  have h3R : 3 ∣ lcmOddPart k := hcop.dvd_of_dvd_mul_left h3L
  exact Nat.le_of_dvd (lcmOddPart_pos k) h3R

def lcmWitness (k : ℕ) : QHilbert := witness (2 ^ (k - 1)) (lcmOddPart k)

theorem lcmWitness_norm_sq_le (k : ℕ) : ‖lcmWitness k‖ ^ 2 ≤ 1 / 4 :=
  witness_norm_sq_le _ _ (by positivity)

theorem lcmWitness_inner_old_cell (k : ℕ) (hk : 2 ≤ k)
    (v : QHilbert) (hv : v ∈ cellSpace (Nat.lcmUpto (2 ^ k - 1))) :
    inner ℝ (lcmWitness k) v = 0 := by
  rw [← lcm_before_two_pow_decomposition k hk] at hv
  exact witness_inner_old_cell _ _ (by positivity) (lcmOddPart_pos k)
    (lcmOddPart_coprime_two k) v hv

/-- Uniform failure of depth decay at every genuine 2^k LCM admission. -/
theorem lcmWitness_revealed_norm_sq_lower (k : ℕ) (hk : 2 ≤ k) :
    (1 / 147 : ℝ) ≤
      ‖conditionalProjection (Nat.lcmUpto (2 ^ k)) (lcmWitness k)‖ ^ 2 := by
  rw [Nat.lcmUpto_prime_pow Nat.prime_two (by omega : k ≠ 0),
    ← lcm_before_two_pow_decomposition k hk]
  simpa only [lcmWitness, Nat.mul_assoc] using
    witness_revealed_norm_sq_lower (2 ^ (k - 1)) (lcmOddPart k) (by positivity)
      (lcmOddPart_ge_three k hk) (lcmOddPart_coprime_two k)

theorem lcmWitness_revealed_relative_lower (k : ℕ) (hk : 2 ≤ k) :
    (4 / 147 : ℝ) * ‖lcmWitness k‖ ^ 2 ≤
      ‖conditionalProjection (Nat.lcmUpto (2 ^ k)) (lcmWitness k)‖ ^ 2 := by
  have h1 := lcmWitness_norm_sq_le k
  have h2 := lcmWitness_revealed_norm_sq_lower k hk
  nlinarith

end RiemannResearch.RH.QGcdCellLCMObstruction
