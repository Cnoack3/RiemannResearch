/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.PrimeTreeCarryMultiplicity
import RiemannResearch.RH.PrimeTreeCanonicalBounds
import RiemannResearch.RH.RiemannHypothesisStrip
import RiemannResearch.RH.ZetaStripReflection
import Mathlib.Tactic

/-! # A single actual carry integral and the left half-strip

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026),
§5.1. Retaining three prime coefficients improves the first lift from
31 to 5 for the RH-equivalent left half-strip.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CanonicalPrimeCarry
open PrimeTreeTwoCarry PrimeTreeSingleLiftBounds

def relativeMultiplier (j : ℕ) (s : ℂ) : ℂ :=
  ((oddChain j).edgeMass 0 : ℂ) +
    (∑' k, ((oddChain j).edgeMass (k+1) : ℂ) * (((radix (k+1) : ℝ)/3 : ℝ) : ℂ)^(1-s)) -
    ((2/3 : ℝ) : ℂ)^(1-s)

theorem multiplier_eq_relative (j : ℕ) (s : ℂ) :
    carryMultiplier j s = (3 : ℂ)^(1-s) / 2 * relativeMultiplier j s := by
  have hs (a : ℝ) (ha : 0 ≤ a) : (3 : ℂ)^(1-s) * ((a/3 : ℝ) : ℂ)^(1-s) = (a : ℂ)^(1-s) := by
    have h := Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 3) (div_nonneg ha (by norm_num : 0 ≤ (3:ℝ))) (1-s)
    have hb : ((3 : ℝ) : ℂ) * ((a/3 : ℝ) : ℂ) = (a : ℂ) := by push_cast; ring
    rw [hb] at h
    simpa using h.symm
  have htail : (3 : ℂ)^(1-s) *
      (∑' k, ((oddChain j).edgeMass (k+1) : ℂ) * (((radix (k+1) : ℝ)/3 : ℝ) : ℂ)^(1-s)) =
      ∑' k, primeMomentTerm j (k+1) s := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [mul_left_comm, hs]
    · simp [primeMomentTerm]
    · positivity
  have h0 : primeMomentTerm j 0 s = ((oddChain j).edgeMass 0 : ℂ) * (3 : ℂ)^(1-s) := by
    simp [primeMomentTerm, radix, primeAt]
  have htwo := hs 2 (by norm_num)
  have he : (2 : ℂ)^(1-s) = 2 * (2 : ℂ)^(-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
  norm_num only [Complex.ofReal_ofNat] at htwo
  rw [he] at htwo
  unfold carryMultiplier relativeMultiplier
  rw [(momentSeries_summable j s).tsum_eq_zero_add, h0]
  linear_combination (1/2 : ℂ)*htwo - (1/2 : ℂ)*htail

theorem five_multiplier_ne (s : ℂ) (hs : 0 ≤ s.re) (hh : s.re ≤ 1/2) : carryMultiplier 2 s ≠ 0 := by
  have he : relativeMultiplier 2 s = fiveFactor (fun k => (radix (k+1) : ℝ)/3)
      (fun k => firstChain.edgeMass (k+1)/5) s := by
    norm_num [relativeMultiplier, fiveFactor, oddChain_edgeMass_zero, oddChain_edgeMass_succ, liftU]
  have hp : 0 < ‖relativeMultiplier 2 s‖ := by
    rw [he]
    exact (by norm_num : (0:ℝ) < 1/300).trans (canonical_fiveFactor_lower s hs hh)
  rw [multiplier_eq_relative]
  exact mul_ne_zero (div_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))) (by norm_num))
    (norm_pos_iff.mp hp)

theorem thirtyOne_relative_lower (s : ℂ) (hs : 0 ≤ s.re) (hh : s.re ≤ 3/4) :
    (11/465 : ℝ) < ‖relativeMultiplier 15 s‖ := by
  let T : ℂ := ∑' k, ((oddChain 15).edgeMass (k+1) : ℂ) * (((radix (k+1) : ℝ)/3 : ℝ) : ℂ)^(1-s)
  let C : ℂ := ((2/3 : ℝ) : ℂ)^(1-s)
  have hT : ‖T‖ ≤ (2/93 : ℝ) * (809/955) := by
    apply le_trans (tsum_of_norm_bounded (canonical_firstMoment.1.hasSum.mul_left (2/93 : ℝ)) ?_)
    · exact mul_le_mul_of_nonneg_left canonical_firstMoment.2 (by norm_num)
    intro k
    have hq : 1 ≤ (radix (k+1) : ℝ)/3 := by
      have hmon : StrictMono primeAt := Nat.nth_strictMono Nat.infinite_setOfPred_prime
      have h := hmon.monotone (show 1 ≤ k+1+1 by omega)
      change primeAt 1 ≤ radix (k+1) at h
      rw [show primeAt 1 = 3 from Nat.nth_prime_one_eq_three] at h
      exact (le_div_iff₀ (by norm_num : (0:ℝ)<3)).mpr (by exact_mod_cast (by simpa using h))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ((oddChain_probability 15).2 _),
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hq), Complex.sub_re, Complex.one_re]
    have hp := Real.rpow_le_rpow_of_exponent_le hq (show 1-s.re ≤ 1 by linarith)
    rw [Real.rpow_one] at hp
    refine (mul_le_mul_of_nonneg_left hp ((oddChain_probability 15).2 _).le).trans_eq ?_
    rw [oddChain_edgeMass_succ]
    norm_num [liftU]
    linear_combination (1/93 : ℝ) * edgeMass_mul_radix (k+1)
  have hC : ‖C‖ < (91/100 : ℝ) := by
    dsimp [C]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2/3), Complex.sub_re, Complex.one_re]
    refine (Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0:ℝ)<2/3) (by norm_num) (show (1/4:ℝ)≤1-s.re by linarith)).trans_lt ?_
    have hf : ((2/3:ℝ)^(1/4:ℝ))^4 = 2/3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2/3)]
      norm_num
    by_contra! h
    have h4 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 91/100) h 4
    rw [hf] at h4
    norm_num at h4
  have hzero : ((oddChain 15).edgeMass 0 : ℂ) = 92/93 := by norm_num [oddChain_edgeMass_zero,liftU]
  have ht : ‖(92/93 : ℂ)‖ ≤ ‖relativeMultiplier 15 s‖ + ‖T‖ + ‖C‖ := by
    have he : (92/93 : ℂ) = (relativeMultiplier 15 s - T) + C := by
      dsimp only [relativeMultiplier,T,C]
      rw [hzero]
      ring
    calc
      _ = ‖(relativeMultiplier 15 s - T) + C‖ := congrArg norm he
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  rw [norm_div] at ht
  norm_num at ht
  linarith

theorem thirtyOne_multiplier_ne (s : ℂ) (hs : 0 ≤ s.re) (hh : s.re ≤ 3/4) : carryMultiplier 15 s ≠ 0 := by
  rw [multiplier_eq_relative]
  exact mul_ne_zero (div_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))) (by norm_num))
    (norm_pos_iff.mp ((by norm_num : (0:ℝ)<11/465).trans (thirtyOne_relative_lower s hs hh)))

/-- The quantitative bound in the paper's original scaling. -/
theorem thirtyOne_scaled_lower (s : ℂ) (hs : 0 ≤ s.re) (hh : s.re ≤ 3/4) :
    (11/465 : ℝ) < ‖(2 : ℂ)^s * carryMultiplier 15 s‖ := by
  have hc (n : ℕ) (hn : 0 < n) (z : ℂ) : ‖(n : ℂ)^z‖ = (n : ℝ)^z.re := by
    simpa only [Complex.ofReal_natCast] using
      Complex.norm_cpow_eq_rpow_re_of_pos (show 0 < (n : ℝ) by exact_mod_cast hn) z
  have hp := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (2 : ℝ) ≤ 3) (show 0 ≤ 1 - s.re by linarith)
  have hprod : (2 : ℝ)^s.re * (2 : ℝ)^(1 - s.re) = 2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), show s.re + (1-s.re) = 1 by ring,
      Real.rpow_one]
  have hb := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s.re)
  rw [hprod] at hb
  have hg : 1 ≤ ‖(2 : ℂ)^s * ((3 : ℂ)^(1-s) / 2)‖ := by
    rw [norm_mul, norm_div, show ‖(2 : ℂ)^s‖ = (2 : ℝ)^s.re from hc 2 (by decide) s,
      show ‖(3 : ℂ)^(1-s)‖ = (3 : ℝ)^(1-s).re from hc 3 (by decide) (1-s),
      Complex.sub_re, Complex.one_re]
    norm_num
    linarith
  rw [multiplier_eq_relative, ← mul_assoc, norm_mul]
  exact (thirtyOne_relative_lower s hs hh).trans_le
    (le_mul_of_one_le_left (norm_nonneg _) hg)

/-- Every zero in the certified range of the U=31 multiplier keeps its order. -/
theorem thirtyOne_readout_order (s : ℂ) (hs : 0 < s.re) (hh : s.re ≤ 3/4) :
    analyticOrderAt (readout (oddChain 15).chainSignal) s = analyticOrderAt riemannZeta s := by
  rw [carry_readout_order 15 s hs (by linarith),
    analyticOrderAt_eq_zero.mpr (Or.inr (thirtyOne_multiplier_ne s hs.le hh)), add_zero]

private theorem single_criterion (j : ℕ)
    (hB : ∀ s : ℂ, 0 < s.re → s.re < 1/2 → carryMultiplier j s ≠ 0) :
    RiemannHypothesis ↔ ∀ s : ℂ, 0 < s.re → s.re < 1/2 → readout (oddChain j).chainSignal s ≠ 0 := by
  have iffzero (s : ℂ) (hs : 0 < s.re) (hh : s.re < 1/2) :
      readout (oddChain j).chainSignal s = 0 ↔ riemannZeta s = 0 := by
    have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at hh
    rw [carry_readout_zeta j s hs hs1]
    simp [hB s hs hh, hs0]
  rw [riemannHypothesis_iff_strip_zeros_on_line]
  constructor
  · intro H s hs hh h
    exact hh.ne (H s ((iffzero s hs hh).mp h) hs (by linarith))
  · intro H s h hs h1
    by_contra! he
    rcases lt_or_gt_of_ne he with hl | hg
    · exact H s hs hl ((iffzero s hs hl).mpr h)
    · have hp : 0 < (1-s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
      have hl : (1-s).re < 1/2 := by rw [Complex.sub_re, Complex.one_re]; linarith
      exact H (1-s) hp hl ((iffzero _ hp hl).mpr (riemannZeta_one_sub_eq_zero_of_strip h hs h1))

theorem rh_iff_five_integral_nonzero :
    RiemannHypothesis ↔ ∀ s : ℂ, 0 < s.re → s.re < 1/2 → readout (oddChain 2).chainSignal s ≠ 0 :=
  single_criterion 2 (fun s hs hh => five_multiplier_ne s hs.le hh.le)

theorem rh_iff_thirtyOne_integral_nonzero :
    RiemannHypothesis ↔ ∀ s : ℂ, 0 < s.re → s.re < 1/2 → readout (oddChain 15).chainSignal s ≠ 0 :=
  single_criterion 15 (fun s hs hh => thirtyOne_multiplier_ne s hs.le (by linarith))

end RiemannResearch.RH.CanonicalPrimeCarry
