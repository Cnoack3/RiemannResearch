/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusLogBootstrapFinite
import RiemannResearch.Analysis.FiniteHarmonicBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensBootstrapCutoffs

/-!
# Logarithmic Mertens improvement from a quantitative prime-error bound

The finite arithmetic identity and explicit cutoff optimization prove the rate
from the displayed Chebyshev-error hypothesis. The unconditional PNT provider
is assembled in `MertensShiftedGlobal`.
-/

open Filter Asymptotics
open scoped Topology BigOperators

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- One unconditional PNT bootstrap gains half a logarithm over the prior
`M(x) log(x) = O(x)` bound. This provider-facing form exposes its exact
quantitative prime-error hypothesis. -/
theorem M_mul_sqrt_log_cube_eventual_of_inverseLogFourth
    (D : ℝ) (hD : 0 ≤ D)
    (hR : ∀ u : ℝ, 1 ≤ u → |R u| ≤ D * u / (1 + Real.log u) ^ 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      |M (N : ℝ)| * (Real.sqrt (Real.log (N : ℝ))) ^ 3 ≤ K * N := by
  have hRtwo : ∀ u : ℝ, 1 ≤ u → |R u| ≤ D * u / (1 + Real.log u) ^ 2 := by
    intro u hu
    have hlog : 0 ≤ Real.log u := Real.log_nonneg hu
    have hsq : 1 ≤ (1 + Real.log u) ^ 2 := by nlinarith [sq_nonneg (Real.log u)]
    have hpow : (1 + Real.log u) ^ 2 ≤ (1 + Real.log u) ^ 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (1 + Real.log u))]
    exact (hR u hu).trans (div_le_div_of_nonneg_left
      (mul_nonneg hD (by linarith)) (by positivity) hpow)
  have hweak : (fun x : ℝ => M x * Real.log x) =O[atTop] id := by
    apply M_mul_log_isBigO_of_sum_abs_R_isBigO
    apply Asymptotics.IsBigO.of_bound (3 * D)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    change abs (∑ k ∈ Finset.Iic ⌊x⌋₊, abs (R (x / k))) ≤ (3 * D) * |x|
    rw [abs_of_nonneg (Finset.sum_nonneg (fun k hk => abs_nonneg _)),
      abs_of_nonneg (show 0 ≤ x by linarith)]
    exact sum_abs_R_le_of_log_square_bound hD hRtwo x hx
  have hweakBound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ y : ℝ in atTop, |M y * Real.log y| ≤ C * y := by
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hweak
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    filter_upwards [hC, eventually_ge_atTop (0 : ℝ)] with y hy hy0
    change |M y * Real.log y| ≤ C * |y| at hy
    rw [abs_of_nonneg hy0] at hy
    exact hy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0)
  obtain ⟨C, hC, hM⟩ := hweakBound
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp hM
  refine ⟨3 + 46 * C + 3 * D, by positivity, ?_⟩
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hloglim.eventually (eventually_ge_atTop ((max 4 Y₀) ^ 2)),
    eventually_ge_atTop (1 : ℕ)] with N hloglarge hN
  let t : ℝ := Real.sqrt (Real.log (N : ℝ))
  have hN0 : 0 < N := by omega
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1R
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = Real.log (N : ℝ) := Real.sq_sqrt hlog0
  have hmax0 : 0 ≤ max (4 : ℝ) Y₀ := by linarith [le_max_left (4 : ℝ) Y₀]
  have htmax : max (4 : ℝ) Y₀ ≤ t := by nlinarith
  have ht4 : 4 ≤ t := (le_max_left _ _).trans htmax
  obtain ⟨Y, J, hY, hYN, hJ, htY, hYt, htJ, hJt, hlogY, hL, hB⟩ :=
    exists_mertens_bootstrap_cutoffs N t hN0 ht4 ht2.symm
  have hY0R : 0 < (Y : ℝ) := by exact_mod_cast hY
  have hlogY0 : 0 < Real.log (Y : ℝ) := by nlinarith
  let A : ℝ := C / Real.log (Y : ℝ)
  have hA : 0 ≤ A := div_nonneg hC (le_of_lt hlogY0)
  have hAC : A * t ^ 2 ≤ 2 * C := by
    dsimp [A]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hlogY0).2
    have he := mul_le_mul_of_nonneg_left hlogY hC
    nlinarith
  have hMtail : ∀ u : ℝ, (Y : ℝ) ≤ u → |M u| ≤ A * u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hY0R hu
    have hu1 : 1 ≤ u := by
      have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY
      linarith
    have huY₀ : Y₀ ≤ u :=
      (le_max_right (4 : ℝ) Y₀).trans (htmax.trans (htY.trans hu))
    have hm := hY₀ u huY₀
    rw [abs_mul, abs_of_nonneg (Real.log_nonneg hu1)] at hm
    have hlogmono := Real.log_le_log hY0R hu
    have hleft := mul_le_mul_of_nonneg_left hlogmono (abs_nonneg (M u))
    have hmul : |M u| * Real.log (Y : ℝ) ≤ C * u := hleft.trans hm
    have hdiv : |M u| ≤ (C * u) / Real.log (Y : ℝ) :=
      (le_div_iff₀ hlogY0).2 hmul
    simpa only [A, div_mul_eq_mul_div] using hdiv
  have hf := M_log_bootstrap_finite N Y J hY hYN hJ A D hA hD hMtail hR
  rw [abs_mul, abs_of_nonneg hlog0, ← ht2] at hf
  have hH : (harmonic J : ℝ) + 1 ≤ 4 * t := by
    have hh := RiemannResearch.Analysis.harmonic_le_index J
    linarith
  have hY1R : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  apply mertens_bootstrap_scalar_unscaled
    (L := Real.log ((N : ℝ) / Y)) (B := Real.log 4 + 5)
    (by exact_mod_cast hN0) (by linarith) hY1R htJ hA hD hYt hAC hH
    (by linarith)
  · simpa only [add_assoc] using hB
  · simpa only [add_assoc] using hf

end RiemannResearch.NumberTheory.PrimeNumberTheorem
