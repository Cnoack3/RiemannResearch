/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeTreeMovingRoot
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Prime number asymptotics at a moving subtree root
The exact formula at the cubic cutoff is combined with the prime number
theorem already available in this project. Source: Section 9 of *Prime trees,
fractional parts, and zeta zeros* (2026). -/

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder

/-- For every sequence of primes tending to infinity, the cubic subtree
has the stated asymptotic, with all analytic inputs proved in the project. -/
theorem cylinder_at_prime_cube_asymptotic (p : ℕ → ℕ) (hp : ∀ n, (p n).Prime)
    (ht : Tendsto p atTop atTop) :
    (fun n => cylinder (p n) (Nat.primesLE (p n)) ((p n)^3)) ~[atTop]
      (fun n => (p n : ℝ)^2 / (2 * Real.log (p n))) := by
  have hcast : Tendsto (fun n => (p n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ht
  have hsq : Tendsto (fun n => (p n)^2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [ht.eventually (eventually_ge_atTop k)] with n hn
    exact hn.trans (by
      simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left (p n) (hp n).one_le)
  have hpnt (t : ℕ → ℕ) (h : Tendsto t atTop atTop) :
      (fun n => (Nat.primeCounting (t n) : ℝ)) ~[atTop]
        (fun n => (t n : ℝ) / Real.log (t n)) := by
    have hh : Tendsto (fun n => (t n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp h
    simpa only [Function.comp_def, Nat.floor_natCast] using pi_alt'.comp_tendsto hh
  have hbig : (fun n => (Nat.primeCounting ((p n)^2) : ℝ)) ~[atTop]
      (fun n => (p n : ℝ)^2 / (2 * Real.log (p n))) := by
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hpnt _ hsq
  have hp0 (n : ℕ) : 0 < (p n : ℝ) := by exact_mod_cast (hp n).pos
  have hl (n : ℕ) : 0 < Real.log (p n) := Real.log_pos (by exact_mod_cast (hp n).one_lt)
  have hsmall : (fun n => (p n : ℝ) / Real.log (p n)) =o[atTop]
      (fun n => (p n : ℝ)^2 / (2 * Real.log (p n))) := by
    apply (isLittleO_iff_tendsto (fun n hn => False.elim ((div_ne_zero (pow_ne_zero _ (hp0 n).ne')
      (mul_ne_zero (by norm_num) (hl n).ne')) hn))).mpr
    have hh : Tendsto (fun n => 2 * (p n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [Function.comp_def, mul_zero] using
        (tendsto_const_nhds (x := (2 : ℝ))).mul (tendsto_inv_atTop_zero.comp hcast)
    apply hh.congr'
    filter_upwards with n
    field_simp [(hp0 n).ne', (hl n).ne']
  have hpi := (hpnt p ht).trans_isLittleO hsmall
  have hcount : Tendsto (fun n => (Nat.primeCounting (p n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Nat.tendsto_primeCounting.comp ht)
  have hone : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n => (Nat.primeCounting (p n) : ℝ)) := by
    apply isLittleO_const_left.mpr (Or.inr ?_)
    simpa [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg] using hcount
  apply ((hbig.sub_isLittleO hpi).sub_isLittleO (hone.trans_isBigO hpi.isBigO)).congr_left
  exact Eventually.of_forall fun n => (cylinder_at_prime_cube (hp n)).symm

/-- The cubic cutoff alone rules out a common constant for prime roots at
every exponent strictly below `2/3`. -/
theorem no_uniform_prime_cube_power_bound {a : ℝ} (ha : a < 2/3) :
    ¬∃ C : ℝ, ∀ p : ℕ, p.Prime →
      |cylinder p (Nat.primesLE p) (p^3)| ≤ C * ((p^3 : ℕ) : ℝ)^a := by
  rintro ⟨C,hC⟩
  choose p hge hp using (fun n : ℕ => Nat.exists_infinite_primes n)
  have ht : Tendsto p atTop atTop := tendsto_atTop.mpr fun k =>
    (eventually_ge_atTop k).mono fun n hn => hn.trans (hge n)
  have hcast : Tendsto (fun n => (p n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp ht
  let w (n : ℕ) := (p n : ℝ)^2 / (2 * Real.log (p n))
  have hx (n : ℕ) : 0 < (p n : ℝ) := by exact_mod_cast (hp n).pos
  have hl (n : ℕ) : 0 < Real.log (p n) := Real.log_pos (by exact_mod_cast (hp n).one_lt)
  have hw (n : ℕ) : 0 < w n :=
    div_pos (pow_pos (hx n) _) (mul_pos (by norm_num) (hl n))
  have hsmall : (fun n => ((p n : ℝ)^3)^a) =o[atTop] w := by
    apply (isLittleO_iff_tendsto (fun n h => ((hw n).ne' h).elim)).mpr
    have hlog := (isLittleO_log_rpow_atTop (show 0 < 2-3*a by linarith)).tendsto_div_nhds_zero
    have ht' : Tendsto (fun n => 2 * (Real.log (p n) / (p n : ℝ)^(2-3*a))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, mul_zero] using
        (tendsto_const_nhds (x := (2:ℝ))).mul (hlog.comp hcast)
    apply ht'.congr'
    filter_upwards with n
    dsimp only [w]
    rw [Real.rpow_sub (hx n), Real.rpow_two,
      show (p n : ℝ)^(3*a) = ((p n : ℝ)^3)^a from Real.rpow_natCast_mul (hx n).le 3 a]
    field_simp [(hx n).ne', (hl n).ne', (Real.rpow_pos_of_pos (pow_pos (hx n) 3) a).ne']
    <;> ring
  have hbound : (fun n => cylinder (p n) (Nat.primesLE (p n)) ((p n)^3)) =O[atTop]
        (fun n => ((p n : ℝ)^3)^a) := by
    apply IsBigO.of_bound C
    filter_upwards with n
    have hn := Real.rpow_nonneg (pow_nonneg (hx n).le 3) a
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn, Nat.cast_pow] using hC (p n) (hp n)
  have hbad : w =o[atTop] w :=
    (cylinder_at_prime_cube_asymptotic p hp ht).isBigO_symm.trans_isLittleO
      (hbound.trans_isLittleO hsmall)
  obtain ⟨n,hn⟩ := (hbad.bound (show (0:ℝ) < 1/2 by norm_num)).exists
  rw [Real.norm_eq_abs, abs_of_pos (hw n)] at hn
  linarith [hw n]

end RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
