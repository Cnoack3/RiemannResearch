/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.OddGapPrimeCorrelation
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Wiener
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # Centered prime correlations for growing odd gaps

The unconditional arithmetic estimate from `OddGapPrimeCorrelation` and the
project's proved `WeakPNT` show that the centered correlation at a growing
odd gap, divided by the interval length, tends to `-1` whenever
`h(N) log(N + h(N) + 2) / N` tends to zero. Every fixed odd gap is a special
case. No prime number theorem hypothesis or zeta-zero hypothesis is assumed.

The power-of-two exceptions are bounded in the imported arithmetic theorem;
the one-point Mangoldt discrepancy is handled here by the actual PNT.
This result does not establish the even-gap cancellation required for the
full triangular prime-correlation asymptotic above Fourier support one.
-/

open scoped BigOperators ArithmeticFunction Topology
open Filter Finset

namespace RiemannResearch.Analysis.OddGapPrimeAsymptotic

open ShortIntervalBoundary ShortIntervalVariance OddGapPrimeCorrelation

theorem nat_add_tendsto (a : ℕ) :
    Tendsto (fun N : ℕ => N + a) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with N hN
  omega

theorem nat_add_ratio_tendsto (a : ℕ) :
    Tendsto (fun N : ℕ => ((N + a : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  have hz : Tendsto (fun N : ℕ => (a : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun N : ℕ => 1 + (a : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hz
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  push_cast
  field_simp

theorem mangoldtMass_eq_range (N : ℕ) :
    mangoldtMass N = ∑ n ∈ range (N + 2), Λ n := by
  have hs := sum_range_add (fun n => Λ n) 2 N
  have hz : (∑ n ∈ range 2, Λ n) = 0 := by norm_num [sum_range_succ]
  simpa only [hz, zero_add, Nat.add_comm 2, mangoldtMass] using hs.symm

/-- The mass of the actual von Mangoldt function has the PNT main term. -/
theorem mangoldtMass_ratio_tendsto :
    Tendsto (fun N : ℕ => mangoldtMass N / (N : ℝ)) atTop (𝓝 1) := by
  have hp := RiemannResearch.NumberTheory.PrimeNumberTheorem.WeakPNT.comp
    (nat_add_tendsto 2)
  have hm := hp.mul (nat_add_ratio_tendsto 2)
  simp only [one_mul] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hn2 : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mangoldtMass_eq_range]
  dsimp only [Function.comp_apply,
    RiemannResearch.NumberTheory.PrimeNumberTheorem.cumsum]
  field_simp

theorem mangoldtMass_error_tendsto :
    Tendsto (fun N : ℕ => |mangoldtMass N - (N : ℝ)| / (N : ℝ))
      atTop (𝓝 0) := by
  have hm :=
    (mangoldtMass_ratio_tendsto.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
  simp only [sub_self, abs_zero] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : mangoldtMass N / (N : ℝ) - 1 =
      (mangoldtMass N - (N : ℝ)) / (N : ℝ) := by
    field_simp
  rw [he, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ N from Nat.cast_nonneg N)]

theorem log_pow_shift_div_tendsto (a k : ℕ) :
    Tendsto (fun N : ℕ => (Real.log ((N + a : ℕ) : ℝ)) ^ k / (N : ℝ))
      atTop (𝓝 0) := by
  have hl := Real.tendsto_pow_log_div_pow_atTop 1 (k : ℝ) (by norm_num)
  simp only [Real.rpow_one, Real.rpow_natCast] at hl
  have ht := hl.comp (tendsto_natCast_atTop_atTop.comp (nat_add_tendsto a))
  have hm := ht.mul (nat_add_ratio_tendsto a)
  simp only [zero_mul] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hna : ((N + a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show N + a ≠ 0 by omega)
  dsimp only [Function.comp_apply]
  field_simp

theorem gap_eventually_le_of_scale (h : ℕ → ℕ)
    (hs : Tendsto (fun N : ℕ =>
      (h N : ℝ) * Real.log ((N + h N + 2 : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 0)) :
    ∀ᶠ N in atTop, h N ≤ N := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : ∀ᶠ N : ℕ in atTop,
      (h N : ℝ) * Real.log ((N + h N + 2 : ℕ) : ℝ) / (N : ℝ) < Real.log 2 :=
    hs.eventually (eventually_lt_nhds hlog2)
  filter_upwards [he, eventually_ge_atTop 1] with N he hN
  by_contra hh
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hhR : (N : ℝ) ≤ h N := by exact_mod_cast (show N ≤ h N by omega)
  have hl : Real.log 2 ≤ Real.log ((N + h N + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num; positivity)
  have ha := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (h N))
  have hb := mul_le_mul_of_nonneg_right hhR hlog2.le
  have hc := (div_lt_iff₀ hN0).mp he
  nlinarith

theorem moving_log_sq_div_tendsto (h : ℕ → ℕ)
    (hh : ∀ᶠ N in atTop, h N ≤ N) :
    Tendsto (fun N : ℕ => (Real.log ((N + h N + 2 : ℕ) : ℝ)) ^ 2 / (N : ℝ))
      atTop (𝓝 0) := by
  have hconst : Tendsto (fun N : ℕ => (2 * (Real.log 4) ^ 2) / (N : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ 2 / (N : ℝ))
      atTop (𝓝 0) := by simpa using log_pow_shift_div_tendsto 0 2
  have hu : Tendsto (fun N : ℕ =>
      (2 * (Real.log 4) ^ 2 + 2 * (Real.log (N : ℝ)) ^ 2) / (N : ℝ))
      atTop (𝓝 0) := by
    convert hconst.add (hlog.const_mul 2) using 1 <;>
      try simp only [add_zero, mul_zero]
    congr 1
    funext N
    ring
  apply squeeze_zero'
    (Eventually.of_forall fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg N))
    _ hu
  filter_upwards [hh, eventually_ge_atTop 1] with N hh hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 ≤ Real.log ((N + h N + 2 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + h N + 2 by omega))
  have hnlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hfour : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hupper : Real.log ((N + h N + 2 : ℕ) : ℝ) ≤
      Real.log 4 + Real.log (N : ℝ) := by
    rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hN0.ne']
    apply Real.log_le_log
    · positivity
    · exact_mod_cast (show N + h N + 2 ≤ 4 * N by omega)
  have hsq := mul_le_mul hupper hupper hL0 (add_nonneg hfour hnlog)
  have hfinal : (Real.log ((N + h N + 2 : ℕ) : ℝ)) ^ 2 ≤
      2 * (Real.log 4) ^ 2 + 2 * (Real.log (N : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (Real.log 4 - Real.log (N : ℝ))]
  exact div_le_div_of_nonneg_right hfinal hN0.le

/-- Actual centered odd-gap correlation, with a growing gap and explicit scale. -/
theorem growing_odd_centered_correlation_tendsto (h : ℕ → ℕ)
    (hodd : ∀ᶠ N in atTop, h N % 2 = 1)
    (hscale : Tendsto (fun N : ℕ =>
      (h N : ℝ) * Real.log ((N + h N + 2 : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => gapCorrelation centeredMangoldt N (h N) / (N : ℝ))
      atTop (𝓝 (-1)) := by
  have hlog := moving_log_sq_div_tendsto h (gap_eventually_le_of_scale h hscale)
  have hbudget : Tendsto (fun N : ℕ =>
      (2 * (Real.log ((N + h N + 2 : ℕ) : ℝ)) ^ 2 +
        2 * |mangoldtMass N - (N : ℝ)| +
        (h N : ℝ) * Real.log ((N + h N + 2 : ℕ) : ℝ)) / (N : ℝ))
      atTop (𝓝 0) := by
    convert ((hlog.const_mul 2).add (mangoldtMass_error_tendsto.const_mul 2)).add hscale
      using 1 <;> try simp only [mul_zero, add_zero]
    congr 1
    funext N
    ring
  have habs : Tendsto (fun N : ℕ =>
      |gapCorrelation centeredMangoldt N (h N) + (N : ℝ)| / (N : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero'
      (Eventually.of_forall fun N => div_nonneg (abs_nonneg _) (Nat.cast_nonneg N))
      _ hbudget
    filter_upwards [hodd] with N hoddN
    exact div_le_div_of_nonneg_right
      (odd_centered_gap_bound N (h N) hoddN) (Nat.cast_nonneg N)
  have hz : Tendsto (fun N : ℕ =>
      (gapCorrelation centeredMangoldt N (h N) + (N : ℝ)) / (N : ℝ))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hden : ∀ N : ℕ, |(N : ℝ)| = (N : ℝ) :=
      fun N => abs_of_nonneg (Nat.cast_nonneg N)
    simpa only [Real.norm_eq_abs, abs_div, hden] using habs
  have ht := hz.sub (tendsto_const_nhds (x := (1 : ℝ)))
  simp only [zero_sub] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp
  ring

/-- For each fixed odd gap, the actual centered correlation has main term `-N`. -/
theorem fixed_odd_centered_correlation_tendsto (h : ℕ) (hodd : h % 2 = 1) :
    Tendsto (fun N : ℕ => gapCorrelation centeredMangoldt N h / (N : ℝ))
      atTop (𝓝 (-1)) := by
  apply growing_odd_centered_correlation_tendsto (fun _ => h)
    (Eventually.of_forall fun _ => hodd)
  have hl := (log_pow_shift_div_tendsto (h + 2) 1).const_mul (h : ℝ)
  simpa only [pow_one, Nat.add_assoc, mul_zero, mul_div_assoc] using hl

end RiemannResearch.Analysis.OddGapPrimeAsymptotic
