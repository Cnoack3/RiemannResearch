/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotEstermannDampedSeries
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact rational twists and coefficient cancellation

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Section 3.3, pp. 116-117, for the arithmetic strategy.
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320

The coefficient cancellation is proved for arbitrary complex exponents and
coefficients and positive real bases. The character and damped-series
identities use arbitrary signed integer numerators, including negative
residue classes. No coprimality is needed for these exact identities.
-/

noncomputable section
open Complex
open scoped BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Gcd reduction gives positive coprime numerator and denominator. -/
theorem reducedRationalTwist_pos_coprime {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    0 < h / h.gcd k ∧ 0 < k / h.gcd k ∧
      (h / h.gcd k).Coprime (k / h.gcd k) :=
  ⟨Nat.div_gcd_pos_of_pos_left k hh, Nat.div_gcd_pos_of_pos_right h hk,
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left k hh)⟩

/-- Exact casts of the reduced fraction, valid even at zero indices. -/
theorem reducedRationalTwist_ratio (F : Type*) [Field F] [CharZero F] (h k : ℕ) :
    ((h / h.gcd k : ℕ) : F) / ((k / h.gcd k : ℕ) : F) = (h : F) / (k : F) := by
  by_cases hh : h = 0
  · simp [hh]
  by_cases hk : k = 0
  · simp [hk]
  have hg : (h.gcd k : F) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.gcd_pos_of_pos_left k (Nat.pos_of_ne_zero hh)).ne'
  rw [Nat.cast_div (Nat.gcd_dvd_left h k) hg, Nat.cast_div (Nat.gcd_dvd_right h k) hg]
  field_simp

/-- The actual coefficient cancellation, strengthened to a complex exponent. -/
theorem rationalTwist_coefficient (A s : ℂ) {m n h k : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hh : 0 < h) (hk : 0 < k) :
    (A * (n:ℂ)^(s-1) / (k:ℂ)^s) * ((m*n*h/k:ℝ):ℂ)^(1-s) =
      (A * (h:ℂ)^(1-s) / (k:ℂ)) * (m:ℂ)^(-(s-1)) := by
  have hp : 0 < m*n*h/k := by positivity
  have hl : Complex.log (((m*n*h/k:ℝ):ℂ)) =
      Complex.log (m:ℂ) + Complex.log (n:ℂ) + Complex.log (h:ℂ) -
        Complex.log (k:ℂ) := by
    rw [← Complex.ofReal_log hp.le, Real.log_div (by positivity) hk.ne',
      Real.log_mul (by positivity) hh.ne', Real.log_mul hm.ne' hn.ne']
    rw [← Complex.ofReal_log hm.le, ← Complex.ofReal_log hn.le,
      ← Complex.ofReal_log hh.le, ← Complex.ofReal_log hk.le]
    push_cast
    rfl
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hk.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hm.ne'), hl]
  rw [← Complex.exp_log (Complex.ofReal_ne_zero.mpr hk.ne')]
  simp only [div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add, mul_assoc]
  simp only [Complex.exp_log (Complex.ofReal_ne_zero.mpr hk.ne')]
  congr 1
  congr 1
  ring

/-- Exact rational additive character for any signed numerator. -/
theorem stdAddChar_rationalTwist {K : ℕ} [NeZero K] (H : ℤ) (m n : ℕ) :
    ZMod.stdAddChar ((H:ZMod K)*(m:ZMod K)*(n:ZMod K)) =
      exp (2*(Real.pi:ℂ)*I*(m:ℂ)*(n:ℂ)*((H:ℂ)/(K:ℂ))) := by
  rw [show (H:ZMod K)*(m:ZMod K)*(n:ZMod K) =
      ((H*(m:ℤ)*(n:ℤ):ℤ):ZMod K) by push_cast; rfl, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- The damping and rational phase combine before any estimate is taken. -/
theorem estermannDampedTerm_intCast {K : ℕ} [NeZero K] (H : ℤ)
    (α β w : ℂ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    estermannDampedTerm (H : ZMod K) α β w (m,n) =
      exp (2*(Real.pi:ℂ)*I*(m:ℂ)*(n:ℂ)*(w+(H:ℂ)/(K:ℂ))) /
        ((m:ℂ)^α * (n:ℂ)^β) := by
  rw [estermannDampedTerm, estermannTerm_intCast H α β hm hn, ← mul_div_assoc,
    ← Complex.exp_add]
  congr 2
  ring

/-- Exact displacement formula for arbitrary complex z and signed integer H. -/
theorem estermannDampedTerm_displacement {K : ℕ} [NeZero K] (H : ℤ)
    (α β z : ℂ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    estermannDampedTerm (H : ZMod K) α β (((H:ℂ)/(K:ℂ))*(z-1)) (m,n) =
      exp (2*(Real.pi:ℂ)*I*(m:ℂ)*(n:ℂ)*((H:ℂ)/(K:ℂ))*z) /
        ((m:ℂ)^α * (n:ℂ)^β) := by
  rw [estermannDampedTerm_intCast H α β _ hm hn]
  congr 2
  ring

/-- Changing the presentation of a rational twist leaves each term unchanged. -/
theorem estermannDampedTerm_rational_congr {K L : ℕ} [NeZero K] [NeZero L]
    (H J : ℤ) (h : (H:ℂ)/(K:ℂ) = (J:ℂ)/(L:ℂ))
    (α β w : ℂ) (p : ℕ × ℕ) :
    estermannDampedTerm (H:ZMod K) α β w p =
      estermannDampedTerm (J:ZMod L) α β w p := by
  rcases p with ⟨m,n⟩
  by_cases hm : m = 0
  · simp [estermannDampedTerm, estermannTerm, hm]
  by_cases hn : n = 0
  · simp [estermannDampedTerm, estermannTerm, hn]
  rw [estermannDampedTerm_intCast H α β w hm hn,
    estermannDampedTerm_intCast J α β w hm hn, h]

/-- Rational-presentation invariance needs no convergence hypothesis. -/
theorem estermannDampedSeries_rational_congr {K L : ℕ} [NeZero K] [NeZero L]
    (H J : ℤ) (h : (H:ℂ)/(K:ℂ) = (J:ℂ)/(L:ℂ)) (α β w : ℂ) :
    estermannDampedSeries (H:ZMod K) α β w =
      estermannDampedSeries (J:ZMod L) α β w := by
  apply tsum_congr
  exact estermannDampedTerm_rational_congr H J h α β w

end RiemannResearch.Analysis.ConreyBaluyot
