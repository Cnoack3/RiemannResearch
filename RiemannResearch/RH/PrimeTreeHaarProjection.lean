/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoResidueUniformCovariance
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Finite Haar least squares for a composite residue against its prime coordinates

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros*, 5 November
2026, §2.2. The error is the centered raw composite residue minus the sum of
the centered raw prime residues, divided by the conductor. The exact uniform
covariance on the full period gives the normal equations and the error energy.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

private def periodPair (d : ℕ) (f g : ℕ → ℝ) : ℝ :=
  (∑ n ∈ Finset.range d, f n * g n) / d

private theorem periodPair_comm (d : ℕ) (f g : ℕ → ℝ) :
    periodPair d f g = periodPair d g f := by simp [periodPair, mul_comm]

private theorem periodPair_sub_left (d : ℕ) (f h g : ℕ → ℝ) :
    periodPair d (f-h) g = periodPair d f g - periodPair d h g := by
  simp only [periodPair, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_div]

private theorem periodPair_sum_left (d : ℕ) (S : Finset ℕ) (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ) :
    periodPair d (∑ p ∈ S, f p) g = ∑ p ∈ S, periodPair d (f p) g := by
  simp only [periodPair, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_div]

private def centeredRawAtom (p n : ℕ) : ℝ := residue p n - ((p : ℝ)-1)/2

def primeHaarResidual (d : ℕ) : ℕ → ℝ :=
  centeredRawAtom d - ∑ p ∈ d.primeFactors, centeredRawAtom p

private theorem periodPair_centered (p q d : ℕ) (hp : 0 < p) (hq : 0 < q) (hd : 0 < d)
    (hpd : p ∣ d) (hqd : q ∣ d) : periodPair d (centeredRawAtom p) (centeredRawAtom q) =
      (((Nat.gcd p q : ℕ) : ℝ)^2-1)/12 :=
  residue_uniform_covariance p q d hp hq hd hpd hqd

private theorem primeHaarResidual_orthogonal (d p : ℕ) (hd : 0 < d) (hp : p ∈ d.primeFactors) :
    periodPair d (primeHaarResidual d) (centeredRawAtom p) = 0 := by
  have hP := (Nat.mem_primeFactors.mp hp).1
  have hpd := (Nat.mem_primeFactors.mp hp).2.1
  rw [primeHaarResidual, periodPair_sub_left, periodPair_sum_left, Finset.sum_eq_single p]
  · rw [periodPair_centered d p d hd hP.pos hd (dvd_refl d) hpd,
      periodPair_centered p p d hP.pos hP.pos hd hpd hpd, Nat.gcd_eq_right hpd, Nat.gcd_self]
    simp
  · intro q hq hqp
    have hQ := (Nat.mem_primeFactors.mp hq).1
    rw [periodPair_centered q p d hQ.pos hP.pos hd (Nat.mem_primeFactors.mp hq).2.1 hpd,
      ((Nat.coprime_primes hQ hP).mpr hqp).gcd_eq_one]
    norm_num
  · exact fun h => (h hp).elim

/-- Exact physical affine residual on the uniform full period. -/
theorem primeHaarResidual_formula (d n : ℕ) (hd : 0 < d) :
    primeHaarResidual d n / (d : ℝ) = residueFraction d n -
      ((((d : ℝ)-1)/(2*d)) + ∑ p ∈ d.primeFactors,
        (p : ℝ)/d * (residueFraction p n - ((p : ℝ)-1)/(2*p))) := by
  have ht : (∑ p ∈ d.primeFactors, (p : ℝ)/d * (residueFraction p n - ((p : ℝ)-1)/(2*p))) =
      (∑ p ∈ d.primeFactors, centeredRawAtom p n) / d := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    unfold centeredRawAtom residue residueFraction
    field_simp [hpR, hdR] <;> ring
  rw [ht]
  simp only [primeHaarResidual, Pi.sub_apply, Finset.sum_apply, centeredRawAtom]
  unfold residueFraction residue
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hdR] <;> ring

/-- The exact mean squared error of the displayed affine projection. -/
theorem primeHaarResidual_energy (d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Finset.range d, (primeHaarResidual d n / (d : ℝ)) ^ 2) / (d : ℝ) =
      (((d : ℝ)^2 - 1) - ∑ p ∈ d.primeFactors, ((p : ℝ)^2 - 1)) / (12 * (d : ℝ)^2) := by
  let R := primeHaarResidual d
  have drop : periodPair d R R = periodPair d (centeredRawAtom d) R := by
    conv_lhs => arg 2; change centeredRawAtom d - ∑ p ∈ d.primeFactors, centeredRawAtom p
    rw [periodPair_sub_left, periodPair_sum_left, Finset.sum_eq_zero, sub_zero]
    intro p hp
    rw [periodPair_comm]
    exact primeHaarResidual_orthogonal d p hd hp
  have cross (p : ℕ) (hp : p ∈ d.primeFactors) :
      periodPair d (centeredRawAtom p) (centeredRawAtom d) = ((p : ℝ)^2-1)/12 := by
    have hpd := (Nat.mem_primeFactors.mp hp).2.1
    rw [periodPair_centered p d d (Nat.mem_primeFactors.mp hp).1.pos hd hd hpd (dvd_refl d),
      Nat.gcd_eq_left hpd]
  have line : periodPair d R R = (((d : ℝ)^2-1) - ∑ p ∈ d.primeFactors, ((p : ℝ)^2-1))/12 := by
    rw [drop, periodPair_comm d (centeredRawAtom d) R]
    change periodPair d (centeredRawAtom d - ∑ p ∈ d.primeFactors, centeredRawAtom p) _ = _
    rw [periodPair_sub_left, periodPair_sum_left, Finset.sum_congr rfl cross,
      periodPair_centered d d d hd hd hd (dvd_refl d) (dvd_refl d), Nat.gcd_self,
      ← Finset.sum_div, sub_div]
    ring
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  change (∑ n ∈ Finset.range d, (R n / (d : ℝ))^2) / (d : ℝ) = _
  calc
    _ = periodPair d R R / (d : ℝ)^2 := by
      simp_rw [div_pow, pow_two (R _)]
      rw [← Finset.sum_div]
      unfold periodPair
      ring
    _ = _ := by rw [line]; field_simp [hdR] <;> ring

/-- Literal mean over a single residue fibre `n = x + p*i`, `i < t`,
with total conductor `p*t`. -/
theorem uniform_residue_fibre_mean (p t x : ℕ) (hp : 0 < p) (ht : 0 < t) (hx : x < p) :
    (∑ i : Fin t, residueFraction (p*t) (x+p*i)) / (t : ℝ) =
      (p : ℝ)/(p*t) * residueFraction p x + (((p : ℝ)*t)-p)/(2*(p*t)) := by
  have hsmall (i : Fin t) : x+p*(i : ℕ) < p*t := calc
    _ < p + p*(i : ℕ) := Nat.add_lt_add_right hx _
    _ = p*((i : ℕ)+1) := by ring
    _ ≤ p*t := Nat.mul_le_mul_left p i.isLt
  simp only [residueFraction, Nat.mod_eq_of_lt (hsmall _), Nat.mod_eq_of_lt hx,
    Nat.cast_add, Nat.cast_mul, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [fin_real_sum]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp [hpR, htR] <;> ring

private theorem periodPair_smul_left (d : ℕ) (t : ℝ) (f g : ℕ → ℝ) :
    periodPair d (t • f) g = t * periodPair d f g := by
  simp only [periodPair, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

private def centeredPrimeSum (d : ℕ) (b : ℕ → ℝ) : ℕ → ℝ :=
  ∑ p ∈ d.primeFactors, b p • centeredRawAtom p

private theorem centeredPrimeSum_pair (d p : ℕ) (hd : 0 < d) (hp : p ∈ d.primeFactors)
    (b : ℕ → ℝ) : periodPair d (centeredPrimeSum d b) (centeredRawAtom p) =
      b p * (((p : ℝ)^2-1)/12) := by
  rw [centeredPrimeSum, periodPair_sum_left, Finset.sum_eq_single p]
  · rw [periodPair_smul_left, periodPair_centered p p d (Nat.mem_primeFactors.mp hp).1.pos
      (Nat.mem_primeFactors.mp hp).1.pos hd (Nat.mem_primeFactors.mp hp).2.1
      (Nat.mem_primeFactors.mp hp).2.1, Nat.gcd_self]
  · intro q hq hqp
    rw [periodPair_smul_left, periodPair_centered q p d (Nat.mem_primeFactors.mp hq).1.pos
      (Nat.mem_primeFactors.mp hp).1.pos hd (Nat.mem_primeFactors.mp hq).2.1 (Nat.mem_primeFactors.mp hp).2.1,
      ((Nat.coprime_primes (Nat.mem_primeFactors.mp hq).1 (Nat.mem_primeFactors.mp hp).1).mpr hqp).gcd_eq_one]
    norm_num
  · exact fun h => (h hp).elim

private theorem centeredPrimeSum_energy (d : ℕ) (hd : 0 < d) (b : ℕ → ℝ) :
    periodPair d (centeredPrimeSum d b) (centeredPrimeSum d b) =
      ∑ p ∈ d.primeFactors, (b p)^2 * (((p : ℝ)^2-1)/12) := by
  conv_lhs => arg 2; unfold centeredPrimeSum
  rw [periodPair_sum_left]
  apply Finset.sum_congr rfl
  intro p hp
  rw [periodPair_smul_left, periodPair_comm, centeredPrimeSum_pair d p hd hp]
  ring

private theorem centeredPrimeSum_residual (d : ℕ) (hd : 0 < d) (b : ℕ → ℝ) :
    periodPair d (centeredPrimeSum d b) (primeHaarResidual d) = 0 := by
  rw [centeredPrimeSum, periodPair_sum_left]
  apply Finset.sum_eq_zero
  intro p hp
  rw [periodPair_smul_left, periodPair_comm, primeHaarResidual_orthogonal d p hd hp, mul_zero]

/-- The squared centered error for *every* prime slope, including every
admissible CRT lift. The first summand is the least-squares error; the signed
slope excess contributes its full diagonal quadratic energy. -/
theorem primeHaarResidual_slope_energy (d : ℕ) (hd : 0 < d) (c : ℕ → ℝ) :
    let residual := fun n =>
      (∑ p ∈ d.primeFactors, (c p / p - 1 / d) * centeredRawAtom p n) - primeHaarResidual d n / d
    (∑ n ∈ Finset.range d, residual n ^ 2) / (d : ℝ) =
      ((((d : ℝ)^2 - 1) - ∑ p ∈ d.primeFactors, ((p : ℝ)^2 - 1)) / (12 * (d : ℝ)^2)) +
        ∑ p ∈ d.primeFactors, ((1 - 1/(p : ℝ)^2)/12) * (c p - (p : ℝ)/d)^2 := by
  let b := fun p : ℕ => c p / p - 1 / d
  let F := centeredPrimeSum d b
  let R := (1 / (d : ℝ)) • primeHaarResidual d
  have hFR : periodPair d F R = 0 := by
    rw [periodPair_comm]
    change periodPair d ((1 / (d : ℝ)) • primeHaarResidual d) F = 0
    rw [periodPair_smul_left, periodPair_comm, centeredPrimeSum_residual d hd b, mul_zero]
  have hRF : periodPair d R F = 0 := (periodPair_comm d R F).trans hFR
  have split : periodPair d (F-R) (F-R) = periodPair d F F + periodPair d R R := by
    rw [periodPair_sub_left, periodPair_comm d F (F-R), periodPair_comm d R (F-R),
      periodPair_sub_left, periodPair_sub_left, hFR, hRF]
    ring
  have hsite (n : ℕ) : (∑ p ∈ d.primeFactors, (c p / p - 1 / d) * centeredRawAtom p n) -
      primeHaarResidual d n / d = (F-R) n := by
    simp only [F, R, centeredPrimeSum, b, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    ring
  have hR : periodPair d R R = ((((d : ℝ)^2 - 1) - ∑ p ∈ d.primeFactors, ((p : ℝ)^2 - 1)) /
      (12 * (d : ℝ)^2)) := by
    convert primeHaarResidual_energy d hd using 1
    unfold periodPair
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    simp only [R, Pi.smul_apply, smul_eq_mul]
    ring
  dsimp only
  simp_rw [hsite, pow_two ((F-R) _)]
  change periodPair d (F-R) (F-R) = _
  rw [split, hR, add_comm, centeredPrimeSum_energy d hd b]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  dsimp only [b]
  field_simp [hpR, hdR] <;> ring

/-- Literal floor-carry variance for every admissible lift of formula (2).
The center in the left side is its exact Haar mean from formula (3). -/
theorem prime_lift_carry_variance (d : ℕ) (hd : 0 < d) (c : ℕ → ℝ)
    (h : ∀ n : ℕ, Int.fract (∑ p ∈ d.primeFactors, c p * residueFraction p n) = residueFraction d n) :
    let mean := (∑ p ∈ d.primeFactors, c p * (((p : ℝ)-1)/(2*p))) - ((d : ℝ)-1)/(2*d)
    (∑ n ∈ Finset.range d, ((⌊∑ p ∈ d.primeFactors, c p * residueFraction p n⌋ : ℝ) - mean)^2) / d =
      ((((d : ℝ)^2 - 1) - ∑ p ∈ d.primeFactors, ((p : ℝ)^2 - 1)) / (12 * (d : ℝ)^2)) +
        ∑ p ∈ d.primeFactors, ((1 - 1/(p : ℝ)^2)/12) * (c p - (p : ℝ)/d)^2 := by
  dsimp only
  rw [← primeHaarResidual_slope_energy d hd c]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  have hn := h n
  unfold Int.fract at hn
  let m := fun p : ℕ => ((p : ℝ)-1)/(2*p)
  have ht : (∑ p ∈ d.primeFactors, (c p / p - 1 / d) * centeredRawAtom p n) =
      ((∑ p ∈ d.primeFactors, c p * residueFraction p n) - (∑ p ∈ d.primeFactors, c p * m p)) -
      ∑ p ∈ d.primeFactors, (p : ℝ)/d * (residueFraction p n - m p) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    unfold centeredRawAtom residue residueFraction m
    field_simp [hpR, hdR] <;> ring
  dsimp only
  rw [ht, primeHaarResidual_formula d n hd]
  dsimp only [m]
  linarith only [hn]

private theorem prime_raw_pair_test_zero (d p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpd : p ∣ d) (hqd : q ∣ d) (hpq : p ≠ q) (φ : ℕ → ℝ) :
    (∑ n ∈ Finset.range d, centeredRawAtom q n * φ (n % p)) = 0 := by
  let F := fun (i j : ℕ) => φ i * ((j : ℝ) - ((q : ℝ)-1)/2)
  have hil : (∑ n : Fin (Nat.lcm p q), F (n.val % p) (n.val % q)) = 0 := by
    have hg : Nat.gcd p q = 1 := ((Nat.coprime_primes hp hq).mpr hpq).gcd_eq_one
    rw [sum_residuePair_eq_crt p q hp.pos hq.pos F, hg, Nat.div_one, Nat.div_one]
    simp only [Nat.one_mul, F]
    apply Finset.sum_eq_zero
    intro x _
    have hx : x.val = 0 := by have hxlt := x.isLt; omega
    simp only [hx, Nat.zero_add, ← Finset.mul_sum, fin_real_centered_sum, mul_zero, Finset.sum_const_zero]
  obtain ⟨t, rfl⟩ := Nat.lcm_dvd hpd hqd
  rw [Finset.sum_range]
  have hh := residuePair_sum_period_mul p q (Nat.lcm p q) t (Nat.dvd_lcm_left p q)
    (Nat.dvd_lcm_right p q) F
  rw [hil, mul_zero] at hh
  simpa only [F, centeredRawAtom, residue, mul_comm] using hh

private theorem composite_raw_pair_test (d p : ℕ) (hd : 0 < d) (hp : 0 < p) (hpd : p ∣ d)
    (φ : ℕ → ℝ) :
    (∑ n ∈ Finset.range d, (centeredRawAtom d n - centeredRawAtom p n) * φ (n % p)) = 0 := by
  let F := fun (i j : ℕ) => (((i : ℝ) - ((d : ℝ)-1)/2) - ((j : ℝ) - ((p : ℝ)-1)/2)) * φ j
  have h := sum_residuePair_eq_crt d p hd hp F
  rw [Nat.lcm_eq_left hpd, Nat.gcd_eq_right hpd, Nat.div_self hp] at h
  have D : (p : ℝ) * ((d / p : ℕ) : ℝ) = (d : ℝ) := by exact_mod_cast Nat.mul_div_cancel' hpd
  have he (x : Fin p) : (∑ i : Fin (d/p), F (x.val + p*i.val) x.val) = 0 := by
    have hterm (i : Fin (d/p)) : F (x.val + p*i.val) x.val =
        ((p : ℝ) * φ x.val) * ((i.val : ℝ)-(((d/p : ℕ) : ℝ)-1)/2) := by
      simp only [F, Nat.cast_add, Nat.cast_mul]
      rw [← D]; ring
    simp only [hterm, ← Finset.mul_sum, fin_real_centered_sum, mul_zero]
  simp only [Fin.sum_univ_one, Fin.val_zero, Nat.mul_zero, Nat.add_zero, he, Finset.sum_const_zero] at h
  rw [Finset.sum_range]
  exact h

/-- The affine residual is orthogonal even to arbitrary tests of one prime
coordinate. This strictly extends the normal equations for the linear atoms. -/
theorem primeHaarResidual_all_site_tests (d p : ℕ) (hd : 0 < d) (hp : p ∈ d.primeFactors) (φ : ℕ → ℝ) :
    (∑ n ∈ Finset.range d, primeHaarResidual d n * φ (n % p)) = 0 := by
  have he := composite_raw_pair_test d p hd (Nat.mem_primeFactors.mp hp).1.pos
    (Nat.mem_primeFactors.mp hp).2.1 φ
  simp only [sub_mul, Finset.sum_sub_distrib] at he
  simp only [primeHaarResidual, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul]
  have hsingle : (∑ q ∈ d.primeFactors, ∑ n ∈ Finset.range d, centeredRawAtom q n * φ (n % p)) =
      ∑ n ∈ Finset.range d, centeredRawAtom p n * φ (n % p) := by
    apply Finset.sum_eq_single p
    · intro q hq hqp
      exact prime_raw_pair_test_zero d p q (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hq).1
        (Nat.mem_primeFactors.mp hp).2.1 (Nat.mem_primeFactors.mp hq).2.1 hqp.symm φ
    · exact fun h => (h hp).elim
  rw [Finset.sum_comm (s := Finset.range d) (t := d.primeFactors), hsingle]
  exact he

end RiemannResearch.RH.Pareto
