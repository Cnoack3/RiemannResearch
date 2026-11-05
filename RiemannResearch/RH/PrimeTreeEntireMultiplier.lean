/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.PrimeTreeOddLift
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-! # The entire multiplier of the explicit carry law

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026),
§5. A ratio test on p_k^m/D_k proves all positive moments directly.
-/

noncomputable section
open Filter Set MeasureTheory
open scoped BigOperators Topology
namespace RiemannResearch.RH.CanonicalPrimeCarry
open CRTCarryArithmetic

private theorem rad_next (k : ℕ) : radix (k+1) ≤ 2 * radix k := by
  obtain ⟨q, hp, hgt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (radix k)
    (primeAt_prime (k+1)).ne_zero
  by_contra! h
  exact hgt.not_ge (Nat.le_nth_of_lt_nth_succ (hle.trans_lt h) hp)

private theorem moment_majorant (m : ℕ) :
    Summable (fun k => (radix k : ℝ)^m / (primorialAt k : ℝ)) := by
  apply summable_of_ratio_norm_eventually_le (by norm_num : (1/2 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop (2^(m+1) : ℕ)] with k hk
  have hmon : StrictMono primeAt := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hrad : 2^(m+1) ≤ radix k := hk.trans ((Nat.le_succ _).trans (hmon.id_le (k+1)))
  have hrr : (2 : ℝ)^(m+1) ≤ (radix k : ℝ) := by exact_mod_cast hrad
  have hp : 0 < (radix k : ℝ) := Nat.cast_pos.mpr (primeAt_prime (k+1)).pos
  have hd : 0 < (primorialAt k : ℝ) := by exact_mod_cast
    (pow_pos (by decide : 0 < (2 : ℕ)) k).trans_le (firstChain.modulus_growth k)
  have hp' : (radix (k+1) : ℝ)^m ≤ (2 : ℝ)^m * (radix k : ℝ)^m := by
    simpa [mul_pow] using pow_le_pow_left₀ (Nat.cast_nonneg (radix (k+1)) : (0 : ℝ) ≤ _)
      (show (radix (k+1) : ℝ) ≤ 2 * (radix k : ℝ) by exact_mod_cast rad_next k) m
  have he : primorialAt (k+1) = primorialAt k * radix k := firstChain.next k
  rw [he, Nat.cast_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (radix (k+1) : ℝ)^m / ((primorialAt k : ℝ) * (radix k : ℝ))),
    abs_of_nonneg (by positivity : 0 ≤ (radix k : ℝ)^m / (primorialAt k : ℝ))]
  apply (div_le_iff₀ (mul_pos hd hp)).mpr
  have halg : 1/2 * ((radix k : ℝ)^m / (primorialAt k : ℝ)) * ((primorialAt k : ℝ) * (radix k : ℝ)) =
      ((radix k : ℝ)/2) * (radix k : ℝ)^m := by field_simp <;> ring
  rw [halg]
  rw [pow_succ] at hrr
  exact hp'.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

theorem oddChain_all_moments (j m : ℕ) :
    Summable (fun k => (oddChain j).edgeMass k * (radix k : ℝ)^m) := by
  apply Summable.of_norm_bounded ((moment_majorant m).mul_left 2)
  intro k
  have hM := (oddChain_probability j).2 k
  have hD : 0 < (primorialAt k : ℝ) := by exact_mod_cast
    (pow_pos (by decide : 0 < (2 : ℕ)) k).trans_le (firstChain.modulus_growth k)
  have hb := (le_abs_self ((oddChain j).w k)).trans ((oddChain j).weight_bound k)
  have hd : (oddChain j).edgeMass k ≤ 2 / (primorialAt k : ℝ) := by
    have hnext : 0 ≤ (oddChain j).w (k+1) / ((oddChain j).D (k+1) : ℝ) :=
      div_nonneg (show 0 ≤ (oddChain j).w (k+1) from (oddWeight_pos j (k+1)).le) (Nat.cast_nonneg _)
    have hh := div_le_div_of_nonneg_right hb hD.le
    change 2 * ((oddChain j).w k / (primorialAt k : ℝ) - _) ≤ _
    calc
      _ ≤ 2 * (1 / (primorialAt k : ℝ)) := mul_le_mul_of_nonneg_left ((sub_le_self _ hnext).trans hh) (by norm_num)
      _ = _ := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM.le (by positivity))]
  calc
    _ ≤ (2 / (primorialAt k : ℝ)) * (radix k : ℝ)^m := mul_le_mul_of_nonneg_right hd (by positivity)
    _ = _ := by ring

def primeMomentTerm (j k : ℕ) (s : ℂ) : ℂ :=
  ((oddChain j).edgeMass k : ℂ) * (radix k : ℂ) ^ (1-s)

def carryMultiplier (j : ℕ) (s : ℂ) : ℂ :=
  (1/2 : ℂ) * (∑' k, primeMomentTerm j k s) - (2 : ℂ)^(-s)

private theorem term_bound (j m k : ℕ) (z : ℂ) (h : 1 - (m : ℝ) < z.re) :
    ‖primeMomentTerm j k z‖ ≤ (oddChain j).edgeMass k * (radix k : ℝ)^m := by
  have hp : 0 < (radix k : ℝ) := Nat.cast_pos.mpr (primeAt_prime _).pos
  have hn := Complex.norm_cpow_eq_rpow_re_of_pos hp (1-z)
  rw [Complex.ofReal_natCast, Complex.sub_re, Complex.one_re] at hn
  unfold primeMomentTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ((oddChain_probability j).2 k), hn]
  apply mul_le_mul_of_nonneg_left _ ((oddChain_probability j).2 k).le
  simpa only [Real.rpow_natCast] using
    Real.rpow_le_rpow_of_exponent_le (show 1 ≤ (radix k : ℝ) by exact_mod_cast (primeAt_prime _).one_lt.le)
      (show 1 - z.re ≤ (m : ℝ) by linarith)

private theorem term_diff (j k : ℕ) : Differentiable ℂ (primeMomentTerm j k) := by
  intro z
  have hn : (radix k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (primeAt_prime _).ne_zero
  have hd : DifferentiableAt ℂ (fun x : ℂ => 1-x) z := by fun_prop
  exact (hd.const_cpow (Or.inl hn)).const_mul ((oddChain j).edgeMass k : ℂ)

theorem momentSeries_summable (j : ℕ) (s : ℂ) : Summable fun k => primeMomentTerm j k s := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 - s.re)
  exact Summable.of_norm_bounded (oddChain_all_moments j m) (fun k => term_bound j m k s (by linarith))

theorem momentSeries_differentiable (j : ℕ) : Differentiable ℂ (fun s => ∑' k, primeMomentTerm j k s) := by
  intro s
  obtain ⟨m, hm⟩ := exists_nat_gt (1 - s.re)
  let U := {z : ℂ | 1 - (m : ℝ) < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hs : s ∈ U := by change (1 - (m : ℝ)) < s.re; linarith
  exact (Complex.differentiableOn_tsum_of_summable_norm (oddChain_all_moments j m)
    (fun k => (term_diff j k).differentiableOn) hU (fun k z hz => term_bound j m k z hz)).differentiableAt
      (hU.mem_nhds hs)

theorem carryMultiplier_entire (j : ℕ) : Differentiable ℂ (carryMultiplier j) := by
  intro s
  have hd : DifferentiableAt ℂ (fun z : ℂ => -z) s := by fun_prop
  exact ((momentSeries_differentiable j s).const_mul (1/2 : ℂ)).sub
    (hd.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0)))

theorem carryMultiplier_one (j : ℕ) : carryMultiplier j 1 = 0 := by
  have ht := (oddChain_probability j).1.tsum_eq
  have hmass : (∑' k, ((oddChain j).edgeMass k : ℂ)) = 1 := by
    rw [← Complex.ofReal_tsum, ht]
    norm_num
  simp [carryMultiplier, primeMomentTerm, hmass, Complex.cpow_neg_one]

private theorem term_deriv_one (j k : ℕ) :
    deriv (primeMomentTerm j k) 1 = -(((oddChain j).edgeMass k : ℂ) * (Real.log (radix k) : ℂ)) := by
  have hp : (radix k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (primeAt_prime _).ne_zero
  have h := ((((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub (hasDerivAt_id (1 : ℂ))).const_cpow
    (Or.inl hp)).const_mul ((oddChain j).edgeMass k : ℂ)).deriv
  have hl := Complex.ofReal_log (show (0 : ℝ) ≤ radix k from Nat.cast_nonneg _)
  change deriv (fun z : ℂ => ((oddChain j).edgeMass k : ℂ) * (radix k : ℂ) ^ (1-z)) 1 = _
  have hlog : Complex.log (radix k : ℂ) = (Real.log (radix k) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hl.symm
  simpa only [Pi.sub_apply, id_eq, sub_self, Complex.cpow_zero, one_mul, zero_sub,
    mul_neg_one, mul_neg, mul_one, hlog] using h

theorem primeLogMoment_derivative (j : ℕ) :
    HasSum (fun k => -(((oddChain j).edgeMass k : ℂ) * (Real.log (radix k) : ℂ)))
      (deriv (fun s => ∑' k, primeMomentTerm j k s) 1) := by
  let U := {z : ℂ | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h := Complex.hasSum_deriv_of_summable_norm (oddChain_all_moments j 1)
    (fun k => (term_diff j k).differentiableOn) hU (fun k z hz => term_bound j 1 k z (by simpa only [Nat.cast_one, sub_self] using (show 0 < z.re from hz)))
    (show (1 : ℂ) ∈ U by norm_num [U])
  simpa only [term_deriv_one] using h

theorem carryMultiplier_deriv_one (j : ℕ) :
    deriv (carryMultiplier j) 1 = (1/2 : ℂ) * ((Real.log 2 : ℂ) -
      ∑' k, ((oddChain j).edgeMass k : ℂ) * (Real.log (radix k) : ℂ)) := by
  have hfirst := (momentSeries_differentiable j 1).hasDerivAt.const_mul (1/2 : ℂ)
  have htwo := (hasDerivAt_id (1 : ℂ)).neg.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  have htotal := (hfirst.sub htwo).deriv
  have hsum := (primeLogMoment_derivative j).tsum_eq
  have hl := Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)
  rw [tsum_neg] at hsum
  rw [← hsum] at htotal
  convert htotal using 1
  · rfl
  · rw [show Complex.log (2 : ℂ) = (Real.log 2 : ℂ) by simpa using hl.symm]
    norm_num [Complex.cpow_neg_one]
    ring

end RiemannResearch.RH.CanonicalPrimeCarry
