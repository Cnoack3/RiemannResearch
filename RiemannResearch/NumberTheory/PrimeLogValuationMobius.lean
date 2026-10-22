/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Floor-logarithm jumps and actual prime valuations

Source: user-provided argument, 21 October 2026: recover the valuation
from floor-logarithm jumps and invert by inclusion-exclusion. The formal
proof uses Mathlib's finite divisor-sum Moebius inversion theorem.

F_p(n) is Nat.log p n, whereas v_p(n) is n.factorization p.
Their link is an exact finite divisor transform:
  v_p(n) = sum_{d|n} (F_p(d)-F_p(d-1)).
Möbius inversion recovers the jump, and ordinary summation recovers F_p.
All integer values at n=0 and n=1 are explicit and harmless.
No closure-preservation or RH assertion is part of these arithmetic identities.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RiemannResearch.NumberTheory.PrimeLogValuationMobius

/-- Ordinary discrete jump, in the integers so subtraction is not truncated. -/
def logJump (p n : ℕ) : ℤ := (Nat.log p n : ℤ) - (Nat.log p (n - 1) : ℤ)

@[simp] theorem logJump_zero (p : ℕ) : logJump p 0 = 0 := by
  simp [logJump]

@[simp] theorem logJump_one (p : ℕ) : logJump p 1 = 0 := by
  simp [logJump]

private theorem log_pred_pow_succ (p k : ℕ) (hp : 1 < p) :
    Nat.log p (p ^ (k + 1) - 1) = k := by
  have hpos : 0 < p ^ k := pow_pos (by omega) _
  have hpow : p ^ (k + 1) = p ^ k * p := pow_succ p k
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · rw [hpow]
    have : p ^ k + 1 ≤ p ^ k * p := by nlinarith
    omega
  · exact Nat.sub_lt (pow_pos (by omega) _) (by omega)

/-- A floor logarithm jumps precisely at the positive powers of its base.
The base need not be prime for this statement. -/
theorem logJump_eq_positive_power_indicator (p n : ℕ) (hp : 1 < p) :
    logJump p n = if ∃ k : ℕ, 0 < k ∧ p ^ k = n then 1 else 0 := by
  classical
  by_cases hpow : ∃ k : ℕ, 0 < k ∧ p ^ k = n
  · rw [if_pos hpow]
    obtain ⟨k, hk, rfl⟩ := hpow
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [logJump, Nat.log_pow hp, log_pred_pow_succ p j hp]
    simp only [Nat.cast_succ]
    ring
  · rw [if_neg hpow]
    have hlogs : Nat.log p n = Nat.log p (n - 1) := by
      by_cases hn : n ≤ 1
      · have hcases : n = 0 ∨ n = 1 := by omega
        rcases hcases with rfl | rfl <;> simp
      · have hn1 : 1 ≤ n := by omega
        have hnminus : n - 1 ≠ 0 := by omega
        have hnot : p ^ Nat.log p n ≠ n := by
          intro he
          have hk : 0 < Nat.log p n := by
            by_contra h
            have hz : Nat.log p n = 0 := by omega
            rw [hz, pow_zero] at he
            omega
          exact hpow ⟨Nat.log p n, hk, he⟩
        have he := (Nat.log_eq_log_succ_iff hp hnminus).mpr
          (by simpa only [Nat.sub_add_cancel hn1] using hnot)
        simpa only [Nat.sub_add_cancel hn1] using he.symm
    simp [logJump, hlogs]

/-- Counting the positive prime-power divisors gives the actual factorization
exponent. This is a finite identity, with the usual zero-divisor convention. -/
theorem sum_divisors_logJump (p n : ℕ) (hp : p.Prime) :
    (∑ d ∈ n.divisors, logJump p d) = (n.factorization p : ℤ) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  · have hcard :
        (Finset.Icc 1 (n.factorization p)).card =
          (n.divisors.filter (fun d => ∃ k : ℕ, 0 < k ∧ p ^ k = d)).card := by
      apply Finset.card_bij (fun k _ => p ^ k)
      · intro k hk
        obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
        apply Finset.mem_filter.mpr
        refine ⟨Nat.mem_divisors.mpr ⟨(hp.pow_dvd_iff_le_factorization hn).mpr hkn, hn⟩,
          ⟨k, by omega, rfl⟩⟩
      · intro a ha b hb hab
        have hlog := congrArg (Nat.log p) hab
        simpa only [Nat.log_pow hp.one_lt] using hlog
      · intro d hd
        obtain ⟨hddiv, ⟨k, hk, hkd⟩⟩ := Finset.mem_filter.mp hd
        refine ⟨k, Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hkd⟩
        apply (hp.pow_dvd_iff_le_factorization hn).mp
        simpa only [hkd] using (Nat.mem_divisors.mp hddiv).1
    have hcard' :
        (n.divisors.filter (fun d => ∃ k : ℕ, 0 < k ∧ p ^ k = d)).card =
          n.factorization p := by
      simpa using hcard.symm
    calc
      (∑ d ∈ n.divisors, logJump p d) =
          ((n.divisors.filter (fun d => ∃ k : ℕ, 0 < k ∧ p ^ k = d)).card : ℤ) := by
        simp_rw [logJump_eq_positive_power_indicator p _ hp.one_lt]
        rw [← Finset.sum_filter]
        simp
      _ = (n.factorization p : ℤ) := by rw [hcard']

/-- Inclusion-exclusion on the divisor lattice recovers the floor-log jump. -/
theorem logJump_eq_moebius_valuation (p n : ℕ) (hp : p.Prime) :
    logJump p n =
      ∑ d ∈ n.divisors,
        ArithmeticFunction.moebius d * ((n / d).factorization p : ℤ) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hforward : ∀ m > 0, (∑ d ∈ m.divisors, logJump p d) =
        (m.factorization p : ℤ) :=
      fun m _ => sum_divisors_logJump p m hp
    have hinverse := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := logJump p) (g := fun m => (m.factorization p : ℤ))).mp hforward
    have h := hinverse n (Nat.pos_of_ne_zero hn)
    simp only [Int.cast_id] at h
    rw [Nat.sum_divisorsAntidiagonal
      (fun a b => ArithmeticFunction.moebius a * (b.factorization p : ℤ))] at h
    exact h.symm

/-- Ordinary summation is the inverse of the discrete jump. -/
theorem sum_logJump_range (p N : ℕ) :
    (∑ k ∈ Finset.range N, logJump p (k + 1)) = (Nat.log p N : ℤ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, logJump]
      simp only [Nat.add_sub_cancel]
      ring

/-- Complete finite recovery of F_p from the actual valuation via Möbius
inversion followed by ordinary cumulative summation. -/
theorem log_eq_cumulative_moebius_valuation (p N : ℕ) (hp : p.Prime) :
    (Nat.log p N : ℤ) =
      ∑ k ∈ Finset.range N, ∑ d ∈ (k + 1).divisors,
        ArithmeticFunction.moebius d * (((k + 1) / d).factorization p : ℤ) := by
  rw [← sum_logJump_range p N]
  apply Finset.sum_congr rfl
  intro k hk
  exact logJump_eq_moebius_valuation p (k + 1) hp

end RiemannResearch.NumberTheory.PrimeLogValuationMobius
