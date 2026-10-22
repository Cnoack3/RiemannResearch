/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.PrimePhaseCRT
import RiemannResearch.Analysis.LagPhase
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Prime phases on the unit additive circle

This module places the exact prime-phase arithmetic on Mathlib's
`AddCircle (1 : ℝ)` and connects it to the actual Fourier characters `fourier`.
Distinct prime coordinates determine every real input exactly. Their
characters have the exact frequency `(k : ℝ) * log p`, and finite products
retain the sum of those frequencies before any estimates are made.

Source for the statements and notation: the user-supplied corrected note
*Prime phases of zeta-zero ordinates: corrected harmonic-analysis note*
(October 11, 2026), Sections 2, 3, and 7. The arithmetic input is the existing
`RiemannResearch.RH.PrimePhaseCRT.intPrimeLogRelation`, proved by unique
factorization. No hypothesis concerning the Riemann Hypothesis, zeta zeros,
zero simplicity, or zero ordinates appears in these results. In particular,
injectivity determines a real ordinate, without determining a zero's real
part or multiplicity.

The finite character identity is an exact algebraic identity. It supplies no
zero-sampled equidistribution theorem or growing-frequency estimate.
-/

noncomputable section

namespace RiemannResearch.Analysis.PrimePhaseTorus

open RiemannResearch.RH.PrimePhaseCRT

open scoped BigOperators

/-- The prime-logarithm phase, with period normalized to one. -/
def primePhase (p : ℕ) (t : ℝ) : AddCircle (1 : ℝ) :=
  (Real.log p / (2 * Real.pi) * t : ℝ)

/-- Each individual prime phase is a continuous map to the unit circle. -/
theorem continuous_primePhase (p : ℕ) : Continuous (primePhase p) := by
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_const.mul continuous_id)

/-- The actual quotient metric keeps the full prime-logarithm slope. -/
theorem primePhase_dist_le (p : ℕ) (s t : ℝ) :
    dist (primePhase p s) (primePhase p t) ≤
      |Real.log p / (2 * Real.pi)| * |s - t| := by
  simpa only [primePhase] using LagPhase.scaled_addCircle_dist_le
    1 (Real.log p / (2 * Real.pi)) s t

/-- Two distinct prime phases determine an arbitrary real input exactly. -/
theorem two_prime_phase_injective {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    Function.Injective (fun t : ℝ => (primePhase p t, primePhase q t)) := by
  intro s t hst
  have hpst : primePhase p s = primePhase p t := congrArg Prod.fst hst
  have hqst : primePhase q s = primePhase q t := congrArg Prod.snd hst
  have hps : ((Real.log p / (2 * Real.pi) * (s - t) : ℝ) :
      AddCircle (1 : ℝ)) = 0 := by
    rw [mul_sub, AddCircle.coe_sub]
    exact sub_eq_zero.mpr hpst
  have hqs : ((Real.log q / (2 * Real.pi) * (s - t) : ℝ) :
      AddCircle (1 : ℝ)) = 0 := by
    rw [mul_sub, AddCircle.coe_sub]
    exact sub_eq_zero.mpr hqst
  obtain ⟨a, ha⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hps
  obtain ⟨b, hb⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hqs
  simp only [zsmul_eq_mul, mul_one] at ha hb
  have hrel : (a : ℝ) * Real.log q = (b : ℝ) * Real.log p := by
    rw [ha, hb]
    ring
  obtain ⟨ha0, _⟩ := intPrimeLogRelation hp hq hpq hrel
  have hzero : Real.log p / (2 * Real.pi) * (s - t) = 0 := by
    rw [← ha, ha0]
    simp
  have hpLog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hden : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (div_ne_zero hpLog hden))

/-- Any indexed phase family containing two distinct prime coordinates is
injective. The other coordinates need no arithmetic assumptions. -/
theorem phase_family_injective {ι : Type*} (primes : ι → ℕ)
    (i j : ι) (hi : (primes i).Prime) (hj : (primes j).Prime)
    (hij : primes i ≠ primes j) :
    Function.Injective (fun t : ℝ => fun k : ι => primePhase (primes k) t) := by
  intro s t hst
  apply two_prime_phase_injective hi hj hij
  exact Prod.ext (congrFun hst i) (congrFun hst j)

/-- The logarithms of distinct primes have an irrational ratio. -/
theorem irrational_prime_log_ratio {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : Irrational (Real.log (p : ℝ) / Real.log (q : ℝ)) := by
  rw [irrational_iff_ne_rational]
  intro a b hb heq
  have hqLog : Real.log (q : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hq.one_lt)).ne'
  have hbReal : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hcross := (div_eq_div_iff hqLog hbReal).mp heq
  have hrel : (b : ℝ) * Real.log p = (a : ℝ) * Real.log q := by
    simpa only [mul_comm] using hcross
  exact hb (intPrimeLogRelation hq hp hpq.symm hrel).1

/-- An actual unit-circle Fourier character evaluated on a prime phase has
exact frequency `k * log p`. This algebraic identity also holds for nonprimes. -/
theorem fourier_primePhase (p : ℕ) (k : ℤ) (t : ℝ) :
    fourier k (primePhase p t) =
      Complex.exp (Complex.I * (((k : ℝ) * Real.log p * t : ℝ) : ℂ)) := by
  unfold primePhase
  rw [fourier_coe_apply]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_intCast, Complex.ofReal_one]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]

/-- A finite torus character has the exact summed logarithmic frequency.
No estimates or infinite expansions are used. -/
theorem finite_prime_phase_character (P : Finset ℕ) (k : ℕ → ℤ) (t : ℝ) :
    (∏ p ∈ P, fourier (k p) (primePhase p t)) =
      Complex.exp (Complex.I *
        (((∑ p ∈ P, (k p : ℝ) * Real.log p) * t : ℝ) : ℂ)) := by
  simp_rw [fourier_primePhase]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_sum,
    Finset.sum_mul, Finset.mul_sum]

end RiemannResearch.Analysis.PrimePhaseTorus

end
