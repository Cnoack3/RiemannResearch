/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Polylogarithmic envelopes from local prime multiplication increments

The arithmetic increment bound is an explicit hypothesis.  Strong induction
on the physical integer telescopes it along prime factors, including repeated
factors.  No independence or Chinese remainder theorem is assumed.

Source of the sparse parent-edge refinement: continuation on 27 October 2026
of the user-supplied PrimeResamplingResearch20261027.md agenda, Sections 6
and 8. Only one chosen prime-factor parent per positive integer is needed.
-/

namespace RiemannResearch.Analysis.PrimeIncrementEnvelope

/-- One prime-multiplication step of the polylogarithmic induction. -/
theorem prime_mul_log_envelope_step
    (f : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) (m p n : ℕ)
    (hp : p.Prime) (hn : 0 < n)
    (hstep : |f (p * n) - f n| ≤
      L * Real.log (p : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m)
    (hprev : |f n - f 1| ≤ L * Real.log (n : ℝ) * (6 + Real.log (n : ℝ)) ^ m) :
    |f (p * n) - f 1| ≤
      L * Real.log ((p * n : ℕ) : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hlog : Real.log ((p * n : ℕ) : ℝ) =
      Real.log (p : ℝ) + Real.log (n : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul]
    · exact_mod_cast hp.ne_zero
    · exact_mod_cast (Nat.ne_of_gt hn)
  have hpow : (6 + Real.log (n : ℝ)) ^ m ≤
      (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m := by
    apply pow_le_pow_left₀ (by linarith)
    rw [hlog]
    linarith
  calc
    |f (p * n) - f 1| = |(f (p * n) - f n) + (f n - f 1)| := by congr 1; ring
    _ ≤ |f (p * n) - f n| + |f n - f 1| := abs_add_le _ _
    _ ≤ L * Real.log (p : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m +
        L * Real.log (n : ℝ) * (6 + Real.log (n : ℝ)) ^ m := add_le_add hstep hprev
    _ ≤ L * Real.log (p : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m +
        L * Real.log (n : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow (mul_nonneg hL hln))
    _ = L * Real.log ((p * n : ℕ) : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m := by
      rw [hlog]
      ring

/-- Uniform local prime increments accumulate to one logarithmic factor.
Only positive integer inputs occur in the hypothesis and conclusion. -/
theorem sub_one_abs_le_of_prime_increments
    (f : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) (m : ℕ)
    (hstep : ∀ p n : ℕ, p.Prime → 0 < n →
      |f (p * n) - f n| ≤ L * Real.log (p : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m)
    (n : ℕ) (hn : 0 < n) :
    |f n - f 1| ≤ L * Real.log (n : ℝ) * (6 + Real.log (n : ℝ)) ^ m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn1 : n = 1
      · simp [hn1]
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
      obtain ⟨q, hq⟩ := hpdvd
      have hqpos : 0 < q := by
        by_contra h
        have hzero : q = 0 := by omega
        simp [hzero] at hq
        omega
      have hqlt : q < n := by nlinarith [hp.two_le]
      have hprev := ih q hqlt hqpos
      have hmul := prime_mul_log_envelope_step f L hL m p q hp hqpos
        (hstep p q hp hqpos) hprev
      simpa only [← hq] using hmul

/-- A prime-increment estimate gives a physical polylogarithmic envelope
with one additional logarithmic power and an explicit finite constant. -/
theorem abs_le_polylog_of_prime_increments
    (f : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) (m : ℕ)
    (hstep : ∀ p n : ℕ, p.Prime → 0 < n →
      |f (p * n) - f n| ≤ L * Real.log (p : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m)
    (n : ℕ) (hn : 0 < n) :
    |f n| ≤ (|f 1| + L) * (6 + Real.log (n : ℝ)) ^ (m + 1) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hbase : 1 ≤ 6 + Real.log (n : ℝ) := by linarith
  have hpow : 1 ≤ (6 + Real.log (n : ℝ)) ^ (m + 1) := by
    have hh : (1 : ℝ) ^ (m + 1) ≤ (6 + Real.log (n : ℝ)) ^ (m + 1) := by gcongr
    simpa using hh
  have hfirst : |f 1| ≤ |f 1| * (6 + Real.log (n : ℝ)) ^ (m + 1) := by
    nlinarith [abs_nonneg (f 1)]
  have hsecond : L * Real.log (n : ℝ) * (6 + Real.log (n : ℝ)) ^ m ≤
      L * (6 + Real.log (n : ℝ)) ^ (m + 1) := by
    rw [pow_succ]
    have hh := mul_le_mul_of_nonneg_left
      (show Real.log (n : ℝ) ≤ 6 + Real.log (n : ℝ) by linarith)
      (mul_nonneg hL (pow_nonneg (by linarith : 0 ≤ 6 + Real.log (n : ℝ)) m))
    nlinarith
  calc
    |f n| = |(f n - f 1) + f 1| := by congr 1; ring
    _ ≤ |f n - f 1| + |f 1| := abs_add_le _ _
    _ ≤ L * Real.log (n : ℝ) * (6 + Real.log (n : ℝ)) ^ m + |f 1| :=
      add_le_add (sub_one_abs_le_of_prime_increments f L hL m hstep n hn) le_rfl
    _ ≤ L * (6 + Real.log (n : ℝ)) ^ (m + 1) +
        |f 1| * (6 + Real.log (n : ℝ)) ^ (m + 1) := add_le_add hsecond hfirst
    _ = (|f 1| + L) * (6 + Real.log (n : ℝ)) ^ (m + 1) := by ring


/-- One chosen descending prime-factor edge per integer suffices for telescoping. -/
theorem sub_one_abs_le_of_prime_parent_increments
    (f : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) (m : ℕ)
    (hstep : ∀ n : ℕ, 1 < n → ∃ p q : ℕ,
      p.Prime ∧ 0 < q ∧ p * q = n ∧
        |f n - f q| ≤ L * Real.log (p : ℝ) * (6 + Real.log (n : ℝ)) ^ m)
    (n : ℕ) (hn : 0 < n) :
    |f n - f 1| ≤ L * Real.log (n : ℝ) * (6 + Real.log (n : ℝ)) ^ m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn1 : n = 1
      · simp [hn1]
      obtain ⟨p, q, hp, hq, hpq, hbound⟩ := hstep n (by omega)
      have hqlt : q < n := by nlinarith [hp.two_le]
      have hprev := ih q hqlt hq
      have hmul := prime_mul_log_envelope_step f L hL m p q hp hq
        (by simpa only [hpq] using hbound) hprev
      simpa only [hpq] using hmul

/-- Sparse parent-edge control gives the same global polylogarithmic envelope. -/
theorem abs_le_polylog_of_prime_parent_increments
    (f : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L) (m : ℕ)
    (hstep : ∀ n : ℕ, 1 < n → ∃ p q : ℕ,
      p.Prime ∧ 0 < q ∧ p * q = n ∧
        |f n - f q| ≤ L * Real.log (p : ℝ) * (6 + Real.log (n : ℝ)) ^ m)
    (n : ℕ) (hn : 0 < n) :
    |f n| ≤ (|f 1| + L) * (6 + Real.log (n : ℝ)) ^ (m + 1) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hbase : 1 ≤ 6 + Real.log (n : ℝ) := by linarith
  have hpow : 1 ≤ (6 + Real.log (n : ℝ)) ^ (m + 1) := one_le_pow₀ hbase
  have hfirst : |f 1| ≤ |f 1| * (6 + Real.log (n : ℝ)) ^ (m + 1) := by
    nlinarith [abs_nonneg (f 1)]
  have hsecond : L * Real.log (n : ℝ) * (6 + Real.log (n : ℝ)) ^ m ≤
      L * (6 + Real.log (n : ℝ)) ^ (m + 1) := by
    rw [pow_succ]
    have hh := mul_le_mul_of_nonneg_left
      (show Real.log (n : ℝ) ≤ 6 + Real.log (n : ℝ) by linarith)
      (mul_nonneg hL (pow_nonneg (by linarith : 0 ≤ 6 + Real.log (n : ℝ)) m))
    nlinarith
  calc
    |f n| = |(f n - f 1) + f 1| := by congr 1; ring
    _ ≤ |f n - f 1| + |f 1| := abs_add_le _ _
    _ ≤ L * Real.log (n : ℝ) * (6 + Real.log (n : ℝ)) ^ m + |f 1| :=
      add_le_add (sub_one_abs_le_of_prime_parent_increments f L hL m hstep n hn) le_rfl
    _ ≤ L * (6 + Real.log (n : ℝ)) ^ (m + 1) +
        |f 1| * (6 + Real.log (n : ℝ)) ^ (m + 1) := add_le_add hsecond hfirst
    _ = (|f 1| + L) * (6 + Real.log (n : ℝ)) ^ (m + 1) := by ring

end RiemannResearch.Analysis.PrimeIncrementEnvelope
