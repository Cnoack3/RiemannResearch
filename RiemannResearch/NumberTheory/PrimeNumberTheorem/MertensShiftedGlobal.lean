/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensStretchedDecay
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusLogBootstrapFinite
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensLogThreeHalvesAssembly
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeErrorInverseLogFourth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter
open scoped Topology

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- Stronger unconditional shifted-log provider from the direct MediumPNT
bootstrap. The original three-halves bound remains a valid special case. -/
theorem M_shiftedLog_stretched_bound :
    ∃ d : ℝ, 0 < d ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * Real.exp
        (-d * ((6 + Real.log x) * Real.log (6 + Real.log x)) ^ ((1 : ℝ) / 11)) :=
  M_stretched_loglog_bound

/-- Converts the natural-index endpoint rate to a global shifted-log bound
on every real argument. The shift makes the small-argument denominator
strictly positive. -/
theorem M_shiftedLog_bound_of_eventual_sqrt_log_cube
    (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ N : ℕ in atTop,
      |M (N : ℝ)| * (Real.sqrt (Real.log (N : ℝ))) ^ 3 ≤ K * N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * (6 + Real.log x) ^ (-3 / 2 : ℝ) := by
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
    (hM.and (hloglim.eventually (eventually_ge_atTop (1 : ℝ))))
  let T : ℕ := max T₀ 1
  let B : ℝ := max (64 * K) ((Real.sqrt (6 + Real.log (T : ℝ))) ^ 3)
  have hT1 : 1 ≤ T := le_max_right _ _
  have hT1R : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hB0 : 0 ≤ B := (by positivity : 0 ≤ 64 * K).trans (le_max_left _ _)
  refine ⟨B, hB0, ?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < 6 + Real.log x := by linarith [Real.log_nonneg hx]
  have hs0 : 0 ≤ Real.sqrt (6 + Real.log x) := Real.sqrt_nonneg _
  have hscube0 : 0 ≤ (Real.sqrt (6 + Real.log x)) ^ 3 := by positivity
  have hcubic : |M x| * (Real.sqrt (6 + Real.log x)) ^ 3 ≤ B * x := by
    let N : ℕ := ⌊x⌋₊
    have hNupper : (N : ℝ) ≤ x := Nat.floor_le (le_of_lt hx0)
    have hNlower : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
    have he : M x = M (N : ℝ) := by simp [N, M]
    by_cases hNT : T ≤ N
    · have hrate := hT₀ N ((le_max_left T₀ 1).trans hNT)
      have hN1 : 1 ≤ N := hT1.trans hNT
      have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      have hN0R : 0 < (N : ℝ) := by linarith
      have hx2N : x ≤ 2 * (N : ℝ) := by linarith
      have hlog2 : Real.log 2 ≤ 1 := by
        have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at hh ⊢
        exact hh
      have hlogx : Real.log x ≤ Real.log (N : ℝ) + 1 := by
        have hh := Real.log_le_log hx0 hx2N
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0R.ne'] at hh
        linarith
      have hsN0 : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
      have hsNsq := Real.sq_sqrt (show 0 ≤ Real.log (N : ℝ) by linarith [hrate.2])
      have hssq := Real.sq_sqrt (le_of_lt hL0)
      have hs : Real.sqrt (6 + Real.log x) ≤ 4 * Real.sqrt (Real.log (N : ℝ)) := by
        nlinarith [hrate.2]
      have hpow := pow_le_pow_left₀ hs0 hs 3
      have hm := mul_le_mul_of_nonneg_left hpow (abs_nonneg (M x))
      have hratemul := mul_le_mul_of_nonneg_left hrate.1 (show (0 : ℝ) ≤ 64 by norm_num)
      have h64 : 64 * K * (N : ℝ) ≤ B * x := by
        calc
          _ ≤ (64 * K) * x := mul_le_mul_of_nonneg_left hNupper (by positivity)
          _ ≤ B * x := mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hx0)
      rw [he] at hm ⊢
      nlinarith only [hm, hratemul, h64]
    · have hNT' : N + 1 ≤ T := by omega
      have hxT : x ≤ (T : ℝ) := by
        have hh : (N : ℝ) + 1 ≤ T := by exact_mod_cast hNT'
        linarith
      have hs : Real.sqrt (6 + Real.log x) ≤ Real.sqrt (6 + Real.log (T : ℝ)) :=
        Real.sqrt_le_sqrt (by linarith [Real.log_le_log hx0 hxT])
      have hpow := pow_le_pow_left₀ hs0 hs 3
      have hright : (Real.sqrt (6 + Real.log x)) ^ 3 ≤ B :=
        hpow.trans (le_max_right _ _)
      calc
        _ ≤ x * (Real.sqrt (6 + Real.log x)) ^ 3 :=
          mul_le_mul_of_nonneg_right (M_abs_le_self (le_of_lt hx0)) hscube0
        _ ≤ x * B := mul_le_mul_of_nonneg_left hright (le_of_lt hx0)
        _ = B * x := by ring
  have hprofile0 : 0 ≤ (6 + Real.log x) ^ (-3 / 2 : ℝ) :=
    Real.rpow_nonneg (le_of_lt hL0) _
  have hcancel : (Real.sqrt (6 + Real.log x)) ^ 3 *
      (6 + Real.log x) ^ (-3 / 2 : ℝ) = 1 := by
    rw [pow_succ, pow_two, Real.sqrt_eq_rpow,
      ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    norm_num
  have hh := mul_le_mul_of_nonneg_right hcubic hprofile0
  simpa only [mul_assoc, hcancel, mul_one] using hh

end RiemannResearch.NumberTheory.PrimeNumberTheorem

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

theorem M_shiftedLog_threeHalves_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ B * x * (6 + Real.log x) ^ (-3 / 2 : ℝ) := by
  obtain ⟨D, hD, hR⟩ := R_inverseLogFourth_bound
  obtain ⟨K, hK, hM⟩ :=
    M_mul_sqrt_log_cube_eventual_of_inverseLogFourth D hD.le hR
  exact M_shiftedLog_bound_of_eventual_sqrt_log_cube K hK hM

end RiemannResearch.NumberTheory.PrimeNumberTheorem
