/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.OddGapPrimeAsymptotic

/-! # Uniform centered prime correlations for odd gaps

For any sequence of eventually odd gaps with `h(N) ≤ N`, the actual
centered von Mangoldt correlation divided by `N` tends to `-1`.
This includes every polynomial gap range contained in `[1, N]`.

The endpoint correction is retained as an exact combination of three
Mangoldt masses. The proved PNT controls their errors uniformly on
`[0, 2N]`: small arguments lie in a fixed finite head, and larger
arguments satisfy the PNT tail bound. No additional prime-distribution
hypothesis or rate in the PNT is assumed.

The even-gap cancellation in the full triangular correlation remains
unresolved; this theorem isolates the odd-gap contribution.
-/

open scoped BigOperators ArithmeticFunction Topology
open Filter Finset
namespace RiemannResearch.Analysis.OddGapPrimeUniform
open ShortIntervalBoundary ShortIntervalVariance OddGapPrimeCorrelation OddGapPrimeAsymptotic

/-- A sublinear error remains negligible at arbitrary arguments in `[0, 2N]`. -/
theorem sublinear_error_on_double_range (f : ℕ → ℝ) (h : ℕ → ℕ)
    (hf : Tendsto (fun N : ℕ => |f N| / (N : ℝ)) atTop (𝓝 0))
    (hh : ∀ᶠ N in atTop, h N ≤ 2 * N) :
    Tendsto (fun N : ℕ => |f (h N)| / (N : ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun N =>
      lt_of_lt_of_le ha (div_nonneg (abs_nonneg _) (Nat.cast_nonneg N))
  · intro b hb
    have he := hf.eventually (eventually_lt_nhds (show 0 < b / 4 by positivity))
    obtain ⟨M, hM⟩ := eventually_atTop.1 he
    let R : ℝ := ∑ n ∈ range (M + 1), |f n|
    have hR : Tendsto (fun N : ℕ => R / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    filter_upwards [hh, eventually_ge_atTop 1,
      hR.eventually (eventually_lt_nhds hb)] with N hh hN hRN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    by_cases hsmall : h N < M + 1
    · have hhead : |f (h N)| ≤ R := by
        exact single_le_sum (fun n hn => abs_nonneg (f n)) (mem_range.mpr hsmall)
      exact lt_of_le_of_lt (div_le_div_of_nonneg_right hhead hN0.le) hRN
    · have hh0 : (0 : ℝ) < h N := by
        exact_mod_cast (show 0 < h N by omega)
      have ht := (div_lt_iff₀ hh0).mp (hM (h N) (by omega))
      have hhR : (h N : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hh
      have hmul := mul_le_mul_of_nonneg_left hhR (show 0 ≤ b / 4 by positivity)
      apply (div_lt_iff₀ hN0).mpr
      nlinarith

/-- Exact shifted-mass correction, retaining both interval endpoints. -/
theorem mangoldtMassBoundary_exact (N h : ℕ) :
    mangoldtMassBoundary N h =
      mangoldtMass (N + h) - mangoldtMass N - mangoldtMass h := by
  simp only [mangoldtMassBoundary, mangoldtMass, sum_range_add, sum_sub_distrib]
  ring

theorem mangoldtMassBoundary_error_bound (N h : ℕ) :
    |mangoldtMassBoundary N h| ≤
      |mangoldtMass (N + h) - ((N + h : ℕ) : ℝ)| +
        |mangoldtMass N - (N : ℝ)| + |mangoldtMass h - (h : ℝ)| := by
  have he : mangoldtMassBoundary N h =
      (mangoldtMass (N + h) - ((N + h : ℕ) : ℝ)) -
        (mangoldtMass N - (N : ℝ)) - (mangoldtMass h - (h : ℝ)) := by
    rw [mangoldtMassBoundary_exact]
    push_cast
    ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)

/-- Uniform odd-gap asymptotic, expressed for every moving gap sequence in `[0, N]`. -/
theorem uniform_odd_centered_correlation_tendsto (h : ℕ → ℕ)
    (hodd : ∀ᶠ N in atTop, h N % 2 = 1)
    (hh : ∀ᶠ N in atTop, h N ≤ N) :
    Tendsto (fun N : ℕ => gapCorrelation centeredMangoldt N (h N) / (N : ℝ))
      atTop (𝓝 (-1)) := by
  let E : ℕ → ℝ := fun k => mangoldtMass k - (k : ℝ)
  have he : Tendsto (fun N : ℕ => |E N| / (N : ℝ)) atTop (𝓝 0) :=
    mangoldtMass_error_tendsto
  have hsmall := sublinear_error_on_double_range E h he
    (hh.mono (fun N hhN => by omega))
  have hlarge := sublinear_error_on_double_range E (fun N => N + h N) he
    (hh.mono (fun N hhN => by omega))
  have hlog := moving_log_sq_div_tendsto h hh
  have hbudget : Tendsto (fun N : ℕ =>
      (2 * (Real.log ((N + h N + 2 : ℕ) : ℝ)) ^ 2 + 3 * |E N| +
        |E (N + h N)| + |E (h N)|) / (N : ℝ)) atTop (𝓝 0) := by
    convert (((hlog.const_mul 2).add (he.const_mul 3)).add hlarge).add hsmall
      using 1 <;> try simp only [mul_zero, add_zero]
    funext N
    ring
  have habs : Tendsto (fun N : ℕ =>
      |gapCorrelation centeredMangoldt N (h N) + (N : ℝ)| / (N : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero'
      (Eventually.of_forall fun N => div_nonneg (abs_nonneg _) (Nat.cast_nonneg N))
      _ hbudget
    filter_upwards [hodd] with N hoddN
    have hg := odd_centered_gap_error_bound N (h N) hoddN
    have hb := mangoldtMassBoundary_error_bound N (h N)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    dsimp only [E]
    linarith
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
end RiemannResearch.Analysis.OddGapPrimeUniform
