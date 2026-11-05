/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimeCRTCarries
import RiemannResearch.RH.ParetoResidueUniformCovariance
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Real lifts of the prime residue expansion

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros*, 5 November
2026, §2.1.  Formula (2) permits arbitrary real candidate coefficients. A
single CRT coordinate tests them one at a time. Formula (3) is the literal
mean of their signed floor over a common period.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimeCRTCarries
open ArithmeticCumulative

private theorem prime_axis (d p : ℕ) (hp : p ∈ d.primeFactors) :
    ∃ n : ℕ, 0 < n ∧ n % p = 1 ∧ ∀ q ∈ d.primeFactors, q ≠ p → n % q = 0 := by
  let z := Nat.chineseRemainderOfFinset (fun q : ℕ => if q = p then 1 else 0)
    id d.primeFactors (fun q hq => (Nat.mem_primeFactors.mp hq).1.ne_zero)
    (by
      intro q hq r hr hqr
      exact (Nat.coprime_primes (Nat.mem_primeFactors.mp hq).1
        (Nat.mem_primeFactors.mp hr).1).mpr hqr)
  have hon : (z : ℕ) % p = 1 := by
    have h := z.prop p hp
    change (z : ℕ) % p = (if p = p then 1 else 0) % p at h
    simpa [Nat.mod_eq_of_lt (Nat.mem_primeFactors.mp hp).1.one_lt] using h
  have hpos : 0 < (z : ℕ) := Nat.pos_of_ne_zero (fun hz => by simp [hz] at hon)
  refine ⟨z, hpos, hon, ?_⟩
  intro q hq hqp
  have h := z.prop q hq
  change (z : ℕ) % q = (if q = p then 1 else 0) % q at h
  simpa [hqp] using h

/-- The full classification, specialized to the canonical least positive
inverse of each complementary factor. -/
theorem real_prime_lift_iff (d : ℕ) (hd : 0 < d) (hsf : Squarefree d) (c : ℕ → ℝ) :
    (∀ n : ℕ, 0 < n → Int.fract (∑ p ∈ d.primeFactors, c p * residueFraction p n) =
      residueFraction d n) ↔
    (∀ p ∈ d.primeFactors, ∃ t : ℤ, c p = (canonicalCoefficient d p : ℝ) + (p : ℝ) * t) := by
  classical
  let a := fun p : ℕ => (canonicalCoefficient d p : ℝ)
  have hcanon (n : ℕ) : Int.fract (∑ p ∈ d.primeFactors, a p * residueFraction p n) =
      residueFraction d n := (canonical_prime_carry d hd hsf n).symm
  constructor
  · intro hc p hp
    obtain ⟨n, hn, hon, hoff⟩ := prime_axis d p hp
    have axis_sum (b : ℕ → ℝ) : (∑ q ∈ d.primeFactors, b q * residueFraction q n) =
        b p / (p : ℝ) := by
      rw [Finset.sum_eq_single p]
      · simp [residueFraction, hon, div_eq_mul_inv]
      · intro q hq hqp
        simp [residueFraction, hoff q hq hqp]
      · exact fun h => (h hp).elim
    have he := (hc n hn).trans (hcanon n).symm
    rw [axis_sum c, axis_sum a] at he
    obtain ⟨t, ht⟩ := Int.fract_eq_fract.mp he
    refine ⟨t, ?_⟩
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero
    field_simp [hpR] at ht
    dsimp only [a] at ht
    linarith only [ht]
  · intro hc n _
    let t (p : ℕ) : ℤ := if hp : p ∈ d.primeFactors then (hc p hp).choose else 0
    have ht (p : ℕ) (hp : p ∈ d.primeFactors) : c p = a p + (p : ℝ) * (t p : ℝ) := by
      simpa only [a, t, dif_pos hp] using (hc p hp).choose_spec
    rw [← hcanon n]
    apply Int.fract_eq_fract.mpr
    refine ⟨∑ p ∈ d.primeFactors, t p * ((n % p : ℕ) : ℤ), ?_⟩
    rw [← Finset.sum_sub_distrib, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero
    rw [ht p hp, Int.cast_mul, Int.cast_natCast]
    unfold residueFraction
    field_simp [hpR] <;> ring

/-- An additive real offset preserving the composite atom at every positive
site is an integer. -/
theorem prime_lift_offset_integral (d : ℕ) (hd : 0 < d) (c : ℕ → ℝ) (b : ℝ)
    (h : ∀ n : ℕ, 0 < n → Int.fract (b + ∑ p ∈ d.primeFactors, c p * residueFraction p n) =
      residueFraction d n) : ∃ z : ℤ, b = (z : ℝ) := by
  have ha (p : ℕ) (hp : p ∈ d.primeFactors) : c p * residueFraction p d = 0 := by
    simp [residueFraction, Nat.mod_eq_zero_of_dvd (Nat.mem_primeFactors.mp hp).2.1]
  have hz := h d hd
  rw [Finset.sum_eq_zero ha, add_zero] at hz
  have hr : residueFraction d d = 0 := by simp [residueFraction]
  rw [hr, Int.fract] at hz
  exact ⟨⌊b⌋, sub_eq_zero.mp hz⟩

private theorem residueFraction_period_sum (L d : ℕ) (hL : 0 < L) (hLd : L ∣ d) :
    (∑ n ∈ Finset.range d, residueFraction L n) = (d : ℝ) * (((L : ℝ)-1)/(2*L)) := by
  change (∑ n ∈ Finset.range d, Pareto.residue L n / (L : ℝ)) = _
  rw [← Finset.sum_div, Pareto.residue_uniform_mean_sum L d hL hLd]
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp [hL0] <;> ring

/-- Exact first equality of (3), in a form that also allows real lifts. -/
theorem prime_lift_mean_carry (d : ℕ) (hd : 0 < d) (hsf : Squarefree d) (c : ℕ → ℝ)
    (hc : ∀ p ∈ d.primeFactors, ∃ t : ℤ,
      c p = (canonicalCoefficient d p : ℝ) + (p : ℝ) * t) :
    (∑ n ∈ Finset.range d, (⌊∑ p ∈ d.primeFactors, c p * residueFraction p n⌋ : ℝ)) / (d : ℝ) =
      (∑ p ∈ d.primeFactors, c p * (((p : ℝ)-1)/(2*p))) - ((d : ℝ)-1)/(2*d) := by
  have h (n : ℕ) : (⌊∑ p ∈ d.primeFactors, c p * residueFraction p n⌋ : ℝ) =
      (∑ p ∈ d.primeFactors, c p * residueFraction p n) - residueFraction d n := by
    by_cases hn : n = 0
    · subst n
      simp [residueFraction]
    · have hh := (real_prime_lift_iff d hd hsf c).mpr hc n (Nat.pos_of_ne_zero hn)
      unfold Int.fract at hh
      linarith
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Finset.sum_comm, residueFraction_period_sum d d hd (dvd_refl d)]
  have hprime (p : ℕ) (hp : p ∈ d.primeFactors) :
      (∑ n ∈ Finset.range d, c p * residueFraction p n) =
        (d : ℝ) * (c p * (((p : ℝ)-1)/(2*p))) := by
    rw [← Finset.mul_sum, residueFraction_period_sum p d (Nat.mem_primeFactors.mp hp).1.pos
      (Nat.mem_primeFactors.mp hp).2.1]
    ring
  rw [Finset.sum_congr rfl hprime, ← Finset.mul_sum]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hdR] <;> ring

/-- The second equality in (3) expresses twice the carry mean in terms of
the sum of the lifts and the signed representative height. -/
theorem prime_lift_mean_carry_half (d : ℕ) (hd : 0 < d) (hsf : Squarefree d) (c : ℕ → ℝ)
    (hc : ∀ p ∈ d.primeFactors, ∃ t : ℤ,
      c p = (canonicalCoefficient d p : ℝ) + (p : ℝ) * t) :
    (∑ n ∈ Finset.range d, (⌊∑ p ∈ d.primeFactors, c p * residueFraction p n⌋ : ℝ)) / (d : ℝ) =
      ((∑ p ∈ d.primeFactors, c p) - 1 - ((∑ p ∈ d.primeFactors, c p / p) - 1 / d)) / 2 := by
  rw [prime_lift_mean_carry d hd hsf c hc]
  have hterm (p : ℕ) (hp : p ∈ d.primeFactors) :
      c p * (((p : ℝ)-1)/(2*p)) = (c p-c p/p)/2 := by
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero
    field_simp [hp0] <;> ring
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_sub_distrib]
  field_simp [hd0] <;> ring

/-- The representative height is an integer, extracted by the physical test
at site one. -/
theorem prime_lift_height_integral (d : ℕ) (hd : 1 < d) (hsf : Squarefree d) (c : ℕ → ℝ)
    (hc : ∀ p ∈ d.primeFactors, ∃ t : ℤ,
      c p = (canonicalCoefficient d p : ℝ) + (p : ℝ)*t) :
    ∃ z : ℤ, (∑ p ∈ d.primeFactors, c p / p) - 1 / (d : ℝ) = z := by
  have h := (real_prime_lift_iff d (by omega) hsf c).mpr hc 1 (by decide)
  have hterm (p : ℕ) (hp : p ∈ d.primeFactors) :
      c p * residueFraction p 1 = c p / p := by
    simp [residueFraction, Nat.mod_eq_of_lt (Nat.mem_primeFactors.mp hp).1.one_lt, div_eq_mul_inv]
  rw [Finset.sum_congr rfl hterm] at h
  have hval : residueFraction d 1 = 1 / (d : ℝ) := by simp [residueFraction, Nat.mod_eq_of_lt hd]
  rw [hval] at h
  exact (Int.fract_eq_iff.mp h).2.2

end RiemannResearch.RH.QPrimeCRTCarries
