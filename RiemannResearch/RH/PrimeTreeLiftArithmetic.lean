/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeLifts
import RiemannResearch.RH.PrimeTreeHaarProjection
import Mathlib.Algebra.Order.Round

/-! # CRT idempotents, prime updates, and extremal representatives

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026), §§2.1–2.2.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimeCRTCarries
open ArithmeticCumulative

/-- Any signed choice of representatives from (2). -/
def liftedCoefficient (d p : ℕ) (t : ℕ → ℤ) : ℤ :=
  (canonicalCoefficient d p : ℤ) + (p : ℤ) * t p

/-- Integer representing a single CRT projector at the full conductor. -/
def primeProjector (d p : ℕ) (t : ℕ → ℤ) : ℤ :=
  (d / p : ℕ) * liftedCoefficient d p t

private theorem squarefree_int_mod_ext (d : ℕ) (hsf : Squarefree d) (x y : ℤ)
    (h : ∀ p ∈ d.primeFactors, (x : ZMod p) = (y : ZMod p)) : (x : ZMod d) = (y : ZMod d) := by
  have hdiv (p : ℕ) (hp : p ∈ d.primeFactors) : (p : ℤ) ∣ x - y := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub, h p hp, sub_self]
  have hcop : (d.primeFactors : Set ℕ).Pairwise (fun p q => IsCoprime (p : ℤ) (q : ℤ)) := by
    intro p hp q hq hpq
    exact ((Nat.coprime_primes (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hq).1).mpr hpq).isCoprime
  have hall := Finset.prod_dvd_of_coprime hcop hdiv
  have hp : (∏ p ∈ d.primeFactors, (p : ℤ)) = (d : ℤ) := by
    simpa only [Nat.cast_prod] using congrArg (fun n : ℕ => (n : ℤ)) (Nat.prod_primeFactors_of_squarefree hsf)
  rw [hp] at hall
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (x-y) d).mpr hall
  simpa only [Int.cast_sub, sub_eq_zero] using hz

/-- A projector has exactly one nonzero prime coordinate. -/
theorem primeProjector_coordinate (d p q : ℕ) (hsf : Squarefree d) (hp : p ∈ d.primeFactors)
    (hq : q ∈ d.primeFactors) (t : ℕ → ℤ) :
    (primeProjector d p t : ZMod q) = if p = q then 1 else 0 := by
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl]
    simp only [primeProjector, liftedCoefficient, Int.cast_mul, Int.cast_add, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, add_zero]
    exact canonicalCoefficient_inverse d p hsf (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1
  · have hcop : q.Coprime p := (Nat.coprime_primes (Nat.mem_primeFactors.mp hq).1
        (Nat.mem_primeFactors.mp hp).1).mpr (Ne.symm hpq)
    have hz : ((d / p : ℕ) : ZMod q) = 0 := by
      apply (ZMod.natCast_eq_zero_iff _ _).mpr
      apply hcop.dvd_mul_left.mp
      have he : p * (d / p) = d := by simpa only [Nat.mul_comm] using Nat.div_mul_cancel (Nat.mem_primeFactors.mp hp).2.1
      rw [he]
      exact (Nat.mem_primeFactors.mp hq).2.1
    simp only [primeProjector, Int.cast_mul, Int.cast_natCast, hz, zero_mul, if_neg hpq]

/-- The projectors for arbitrary signed representatives form a complete orthogonal
family of idempotents in the composite ring. -/
theorem primeProjectors_idempotents (d : ℕ) (hsf : Squarefree d) (t : ℕ → ℤ) :
    (∀ p ∈ d.primeFactors, (primeProjector d p t : ZMod d)^2 = (primeProjector d p t : ZMod d)) ∧
    (∀ p ∈ d.primeFactors, ∀ q ∈ d.primeFactors, p ≠ q →
      (primeProjector d p t : ZMod d) * (primeProjector d q t : ZMod d) = 0) ∧
    (∑ p ∈ d.primeFactors, (primeProjector d p t : ZMod d)) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have h := squarefree_int_mod_ext d hsf ((primeProjector d p t)^2) (primeProjector d p t) (by
      intro q hq
      rw [Int.cast_pow, primeProjector_coordinate d p q hsf hp hq t]
      split <;> simp)
    simpa only [Int.cast_pow] using h
  · intro p hp q hq hpq
    have h := squarefree_int_mod_ext d hsf (primeProjector d p t * primeProjector d q t) 0 (by
      intro r hr
      rw [Int.cast_mul, Int.cast_zero, primeProjector_coordinate d p r hsf hp hr t,
        primeProjector_coordinate d q r hsf hq hr t]
      by_cases hpr : p = r
      · subst r
        simp [hpq.symm]
      · simp [hpr])
    simpa only [Int.cast_mul, Int.cast_zero] using h
  · have h := squarefree_int_mod_ext d hsf (∑ p ∈ d.primeFactors, primeProjector d p t) 1 (by
      intro q hq
      simp only [Int.cast_sum, Int.cast_one]
      rw [Finset.sum_eq_single q]
      · simpa using primeProjector_coordinate d q q hsf hq hq t
      · intro p hp hpq
        simpa [hpq] using primeProjector_coordinate d p q hsf hp hq t
      · exact fun hn => (hn hq).elim)
    simpa only [Int.cast_sum, Int.cast_one] using h

/-- On appending a fresh prime q, the retained signed coefficient at p is
multiplied by the inverse of q modulo p, for arbitrary old and new lifts. -/
theorem fresh_prime_lift_update (d p q : ℕ) (hsf : Squarefree d) (hp : p ∈ d.primeFactors)
    (hq : q.Prime) (hfresh : ¬ q ∣ d) (s t : ℕ → ℤ) :
    (liftedCoefficient (d*q) p t : ZMod p) = (q : ZMod p)⁻¹ * (liftedCoefficient d p s : ZMod p) := by
  have hpP := (Nat.mem_primeFactors.mp hp).1
  have hpd := (Nat.mem_primeFactors.mp hp).2.1
  have hpq : q ≠ p := by rintro rfl; exact hfresh hpd
  have hsf' := (Nat.squarefree_mul (hq.coprime_iff_not_dvd.mpr hfresh).symm).mpr ⟨hsf, hq.squarefree⟩
  have hnew := canonicalCoefficient_inverse (d*q) p hsf' hpP (dvd_mul_of_dvd_left hpd q)
  have hold := canonicalCoefficient_inverse d p hsf hpP hpd
  have he : (d*q) / p = (d/p)*q := by
    obtain ⟨m, h⟩ := hpd
    rw [h, Nat.mul_assoc, Nat.mul_div_cancel_left _ hpP.pos, Nat.mul_div_cancel_left _ hpP.pos]
  rw [he, Nat.cast_mul, mul_assoc] at hnew
  have step : (q : ZMod p) * (canonicalCoefficient (d*q) p : ZMod p) = (canonicalCoefficient d p : ZMod p) := by
    calc
      _ = ((canonicalCoefficient d p : ZMod p) * ((d/p : ℕ) : ZMod p)) *
          ((q : ZMod p) * (canonicalCoefficient (d*q) p : ZMod p)) := by
            rw [mul_comm (canonicalCoefficient d p : ZMod p), hold, one_mul]
      _ = _ := by rw [mul_assoc, hnew, mul_one]
  have hu := (ZMod.isUnit_iff_coprime q p).mpr ((Nat.coprime_primes hq hpP).mpr hpq)
  have hi : (q : ZMod p)⁻¹ * q = 1 := by rw [mul_comm]; exact ZMod.mul_inv_of_unit _ hu
  simp only [liftedCoefficient, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, add_zero]
  rw [← step, ← mul_assoc, hi, one_mul]

/-- For at least two prime factors the height of the least-positive representatives
is an integer between one and the number of factors minus one. -/
theorem canonical_height_bounds (d : ℕ) (hsf : Squarefree d) (hk : 2 ≤ d.primeFactors.card) :
    ∃ h : ℤ, (∑ p ∈ d.primeFactors, (canonicalCoefficient d p : ℝ) / p) - 1/(d : ℝ) = h ∧
      1 ≤ h ∧ h ≤ (d.primeFactors.card : ℤ) - 1 := by
  have hne : d.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p0,h0⟩ := hne
  have hd : 1 < d := (Nat.mem_primeFactors.mp h0).1.one_lt.trans_le
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp h0).2.2) (Nat.mem_primeFactors.mp h0).2.1)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc : ∀ p ∈ d.primeFactors, ∃ t : ℤ,
      (canonicalCoefficient d p : ℝ) = (canonicalCoefficient d p : ℝ) + (p : ℝ)*t := by
    intro p _
    exact ⟨0, by simp⟩
  obtain ⟨h,hh⟩ := prime_lift_height_integral d hd hsf _ hc
  have hlo (p : ℕ) (hp : p ∈ d.primeFactors) : 1/(d : ℝ) ≤ (canonicalCoefficient d p : ℝ)/p := by
    obtain ⟨hpP, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpP.pos
    apply (one_div_le_one_div_of_le hpR (by exact_mod_cast Nat.le_of_dvd (show 0 < d by omega) hpd)).trans
    apply div_le_div_of_nonneg_right _ hpR.le
    exact_mod_cast (canonicalCoefficient_bounds d p hsf hpP hpd).1
  have hhi (p : ℕ) (hp : p ∈ d.primeFactors) : (canonicalCoefficient d p : ℝ)/p < 1 := by
    obtain ⟨hpP, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    apply (div_lt_one (by exact_mod_cast hpP.pos : (0 : ℝ) < p)).mpr
    exact_mod_cast (canonicalCoefficient_bounds d p hsf hpP hpd).2
  have hsumlo : (d.primeFactors.card : ℝ)*(1/d) ≤ ∑ p ∈ d.primeFactors, (canonicalCoefficient d p : ℝ)/p := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hlo
  have hsumhi : (∑ p ∈ d.primeFactors, (canonicalCoefficient d p : ℝ)/p) < d.primeFactors.card := by
    simpa using Finset.sum_lt_sum_of_nonempty ⟨p0,h0⟩ hhi
  have hkR : (1 : ℝ) < d.primeFactors.card := by exact_mod_cast (show 1 < d.primeFactors.card by omega)
  have hstrict : 1/(d : ℝ) < (d.primeFactors.card : ℝ)*(1/d) := by
    simpa only [one_mul] using (mul_lt_mul_of_pos_right hkR (one_div_pos.mpr hdR))
  have hlR : (0 : ℝ) < h := by linarith only [hh, hsumlo, hstrict]
  have huR : (h : ℝ) < d.primeFactors.card := by linarith only [hh, hsumhi, one_div_pos.mpr hdR]
  have hlZ : (0 : ℤ) < h := by exact_mod_cast hlR
  have huZ : h < (d.primeFactors.card : ℤ) := by exact_mod_cast huR
  exact ⟨h, hh, by omega, by omega⟩

/-- The variance of the integer floor carry over every site of a full CRT period. -/
def liftedCarryVariance (d : ℕ) (t : ℕ → ℤ) : ℝ :=
  let c := fun p : ℕ => (liftedCoefficient d p t : ℝ)
  let mean := (∑ p ∈ d.primeFactors, c p * (((p : ℝ)-1)/(2*p))) - ((d : ℝ)-1)/(2*d)
  (∑ n ∈ Finset.range d, ((⌊∑ p ∈ d.primeFactors, c p * residueFraction p n⌋ : ℝ)-mean)^2)/d

private theorem liftedCarryVariance_formula (d : ℕ) (hd : 0 < d) (hsf : Squarefree d) (t : ℕ → ℤ) :
    liftedCarryVariance d t =
      (((d : ℝ)^2-1) - ∑ p ∈ d.primeFactors, ((p : ℝ)^2-1)) / (12*(d : ℝ)^2) +
        ∑ p ∈ d.primeFactors, ((1-1/(p : ℝ)^2)/12) * ((liftedCoefficient d p t : ℝ) - (p : ℝ)/d)^2 := by
  apply Pareto.prime_lift_carry_variance d hd
  have hc : ∀ p ∈ d.primeFactors, ∃ u : ℤ,
      (liftedCoefficient d p t : ℝ) = (canonicalCoefficient d p : ℝ) + (p : ℝ)*u := by
    intro p _
    exact ⟨t p, by simp [liftedCoefficient]⟩
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [residueFraction]
  · exact (real_prime_lift_iff d hd hsf _).mpr hc n hn

/-- Every coordinatewise nearest choice minimizes the literal variance. This
permits either integer representative when the distances are equal. -/
theorem nearest_lifts_minimize_variance (d : ℕ) (hd : 0 < d) (hsf : Squarefree d) (s t : ℕ → ℤ)
    (h : ∀ p ∈ d.primeFactors, |(liftedCoefficient d p s : ℝ) - (p : ℝ)/d| ≤
      |(liftedCoefficient d p t : ℝ) - (p : ℝ)/d|) :
    liftedCarryVariance d s ≤ liftedCarryVariance d t := by
  rw [liftedCarryVariance_formula d hd hsf s, liftedCarryVariance_formula d hd hsf t]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro p hp
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_lt.le
  have hsq : (1 : ℝ) ≤ (p : ℝ)^2 := by nlinarith [sq_nonneg ((p : ℝ)-1)]
  have hpos : 0 < (p : ℝ)^2 := by linarith only [hsq]
  have hw : 0 ≤ (1-1/(p : ℝ)^2)/12 := by linarith [(div_le_one hpos).mpr hsq]
  apply mul_le_mul_of_nonneg_left _ hw
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (h p hp)

/-- The independent integer shifts obtained by rounding on each prime lattice. -/
def nearestLiftShift (d p : ℕ) : ℤ :=
  round (((p : ℝ)/d - (canonicalCoefficient d p : ℝ))/p)

/-- Explicit simultaneous minimizer of carry variance over *every* signed lift. -/
theorem rounded_lifts_minimize_variance (d : ℕ) (hd : 0 < d) (hsf : Squarefree d) (t : ℕ → ℤ) :
    liftedCarryVariance d (nearestLiftShift d) ≤ liftedCarryVariance d t := by
  apply nearest_lifts_minimize_variance d hd hsf
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let u := ((p : ℝ)/d - (canonicalCoefficient d p : ℝ))/p
  have hform (z : ℤ) : |(canonicalCoefficient d p : ℝ) + (p : ℝ)*z - (p : ℝ)/d| =
      (p : ℝ)*|u-z| := by
    calc
      _ = |(p : ℝ)*((z : ℝ)-u)| := by
        congr 1
        dsimp only [u]
        field_simp [hpR.ne', hdR.ne'] <;> ring
      _ = _ := by rw [abs_mul, abs_of_pos hpR, abs_sub_comm (z : ℝ) u]
  simp only [liftedCoefficient, Int.cast_add, Int.cast_mul, Int.cast_natCast, hform]
  exact mul_le_mul_of_nonneg_left (round_le u (t p)) hpR.le

end RiemannResearch.RH.QPrimeCRTCarries
