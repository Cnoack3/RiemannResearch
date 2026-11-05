/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusLogBootstrapFinite
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeErrorStretched

/-!
# Finite signed bootstrap with stretched exponential prime error

See `RH/MertensStretchedContinuation20260927.md` for the provider audit,
finite optimization, and scope of the result.
-/

noncomputable section
open Filter Finset
open scoped BigOperators

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

theorem R_stretched_head_bound_rpow (α : ℝ) (hα : 0 ≤ α) (N Y : ℕ) (hY : 0 < Y) (hYN : Y ≤ N)
    (c D : ℝ) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hR : ∀ u : ℝ, 1 ≤ u →
      |R u| ≤ D * u * Real.exp (-c * (Real.log u) ^ α) /
        (1 + Real.log u) ^ 2) :
    |∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d)| ≤
      3 * D * N * Real.exp (-c * (Real.log ((N : ℝ) / Y)) ^ α) := by
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have hNr : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hY hYN
  have hNY : (1 : ℝ) ≤ (N : ℝ) / Y := (le_div_iff₀ hYr).mpr (by
    simpa only [one_mul] using (show (Y : ℝ) ≤ (N : ℝ) by exact_mod_cast hYN))
  have hlogNY : 0 ≤ Real.log ((N : ℝ) / Y) := Real.log_nonneg hNY
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 Y) :
      |(ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d)| ≤
        (D * N * Real.exp (-c * (Real.log ((N : ℝ) / Y)) ^ α)) *
          (1 / ((d : ℝ) * (1 + Real.log ((N : ℝ) / d)) ^ 2)) := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hdY : (d : ℝ) ≤ Y := by exact_mod_cast (Finset.mem_Icc.mp hd).2
    have hNd : (1 : ℝ) ≤ (N : ℝ) / d :=
      (le_div_iff₀ hdpos).mpr (by
        simpa only [one_mul] using
          hdY.trans (show (Y : ℝ) ≤ (N : ℝ) by exact_mod_cast hYN))
    have hlogNd : 0 ≤ Real.log ((N : ℝ) / d) := Real.log_nonneg hNd
    have hlogs : Real.log ((N : ℝ) / Y) ≤ Real.log ((N : ℝ) / d) := by
      apply Real.log_le_log (by positivity)
      exact div_le_div_of_nonneg_left hNr.le hdpos hdY
    have hdecay :
        Real.exp (-c * (Real.log ((N : ℝ) / d)) ^ α) ≤
          Real.exp (-c * (Real.log ((N : ℝ) / Y)) ^ α) := by
      apply Real.exp_le_exp.mpr
      have hp := Real.rpow_le_rpow hlogNY hlogs hα
      nlinarith
    have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [abs_mul]
    calc
      _ ≤ |R ((N : ℝ) / d)| := mul_le_of_le_one_left (abs_nonneg _) hmu
      _ ≤ D * ((N : ℝ) / d) *
          Real.exp (-c * (Real.log ((N : ℝ) / d)) ^ α) /
          (1 + Real.log ((N : ℝ) / d)) ^ 2 := hR _ hNd
      _ = (D * N * Real.exp (-c * (Real.log ((N : ℝ) / d)) ^ α)) *
          (1 / ((d : ℝ) * (1 + Real.log ((N : ℝ) / d)) ^ 2)) := by field_simp <;> ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdecay (mul_nonneg hD hNr.le))
        positivity
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 Y,
        |(ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 Y,
        (D * N * Real.exp (-c * (Real.log ((N : ℝ) / Y)) ^ α)) *
          (1 / ((d : ℝ) * (1 + Real.log ((N : ℝ) / d)) ^ 2)) :=
      Finset.sum_le_sum hterm
    _ = (D * N * Real.exp (-c * (Real.log ((N : ℝ) / Y)) ^ α)) *
        ∑ d ∈ Finset.Icc 1 Y, 1 / ((d : ℝ) * (1 + Real.log ((N : ℝ) / d)) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (D * N * Real.exp (-c * (Real.log ((N : ℝ) / Y)) ^ α)) * 3 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [positive_sum_eq_range_succ]
      simpa only [Nat.cast_add, Nat.cast_one] using
        finite_reciprocal_square_log_sum_le (N : ℝ) Y hY (by exact_mod_cast hYN)
    _ = _ := by ring

theorem R_stretched_head_bound (N Y : ℕ) (hY : 0 < Y) (hYN : Y ≤ N)
    (c D : ℝ) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hR : ∀ u : ℝ, 1 ≤ u →
      |R u| ≤ D * u * Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 10)) /
        (1 + Real.log u) ^ 2) :
    |∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d)| ≤
      3 * D * N * Real.exp (-c * (Real.log ((N : ℝ) / Y)) ^ ((1 : ℝ) / 10)) :=
  R_stretched_head_bound_rpow (1 / 10) (by norm_num) N Y hY hYN c D hc hD hR

theorem M_log_bootstrap_finite_stretched_rpow (α : ℝ) (hα : 0 ≤ α) (N Y J : ℕ) (hY : 0 < Y) (hYN : Y ≤ N)
    (hJ : 0 < J) (A c D : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hM : ∀ t : ℝ, (Y : ℝ) ≤ t → |M t| ≤ A * t)
    (hR : ∀ u : ℝ, 1 ≤ u →
      |R u| ≤ D * u * Real.exp (-c * (Real.log u) ^ α) /
        (1 + Real.log u) ^ 2) :
    |M (N : ℝ) * Real.log N| ≤
      (Y : ℝ) + A * N +
      (N : ℝ) * (1 / (J : ℝ) + 1 / ((Y : ℝ) * J) + A * ((harmonic J : ℝ) + 1)) +
      3 * D * N * Real.exp (-c * (Real.log ((N : ℝ) / Y)) ^ α) +
      2 * A * N * (Real.log ((N : ℝ) / Y) + Real.log 4 + 5) := by
  rw [M_log_bootstrap_identity N Y hY hYN]
  have hL := mobius_log_div_abs_le_cutoff N Y hYN A hA hM
  have hm := mobiusReciprocalSum_cutoff_bound_of_uniform_M_bound Y J hY hJ A hA hM
  have hh := R_stretched_head_bound_rpow α hα N Y hY hYN c D hc hD hR
  have ht := mobius_Psi_tail_abs_le_log N Y hY hYN A hA hM
  have hmn := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) N)
  have h1 := abs_sub (∑ d ∈ Finset.Iic N, (ArithmeticFunction.moebius d : ℝ) *
    Real.log ((N : ℝ) / d)) ((N : ℝ) * RiemannResearch.RH.Pareto.mobiusReciprocalSum Y)
  have h2 := abs_sub ((∑ d ∈ Finset.Iic N, (ArithmeticFunction.moebius d : ℝ) *
    Real.log ((N : ℝ) / d)) - (N : ℝ) * RiemannResearch.RH.Pareto.mobiusReciprocalSum Y)
    (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d))
  have h3 := abs_sub (((∑ d ∈ Finset.Iic N, (ArithmeticFunction.moebius d : ℝ) *
    Real.log ((N : ℝ) / d)) - (N : ℝ) * RiemannResearch.RH.Pareto.mobiusReciprocalSum Y) -
    (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d)))
    (∑ d ∈ Finset.Ioc Y N, (ArithmeticFunction.moebius d : ℝ) * Psi ((N : ℝ) / d))
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)] at h1
  linarith

theorem M_log_bootstrap_finite_stretched (N Y J : ℕ) (hY : 0 < Y) (hYN : Y ≤ N)
    (hJ : 0 < J) (A c D : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hM : ∀ t : ℝ, (Y : ℝ) ≤ t → |M t| ≤ A * t)
    (hR : ∀ u : ℝ, 1 ≤ u →
      |R u| ≤ D * u * Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 10)) /
        (1 + Real.log u) ^ 2) :
    |M (N : ℝ) * Real.log N| ≤
      (Y : ℝ) + A * N +
      (N : ℝ) * (1 / (J : ℝ) + 1 / ((Y : ℝ) * J) + A * ((harmonic J : ℝ) + 1)) +
      3 * D * N * Real.exp (-c * (Real.log ((N : ℝ) / Y)) ^ ((1 : ℝ) / 10)) +
      2 * A * N * (Real.log ((N : ℝ) / Y) + Real.log 4 + 5) :=
  M_log_bootstrap_finite_stretched_rpow (1 / 10) (by norm_num) N Y J hY hYN hJ A c D hA hc hD hM hR

theorem R_stretched_head_bound_unconditional :
    ∃ c > 0, ∃ D > 0, ∀ N Y : ℕ, 0 < Y → Y ≤ N →
      |∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d)| ≤
        3 * D * N * Real.exp (-c * (Real.log ((N : ℝ) / Y)) ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c, hc, D, hD, hR⟩ := R_stretched_squareLog_bound
  refine ⟨c, hc, D, hD, ?_⟩
  intro N Y hY hYN
  exact R_stretched_head_bound N Y hY hYN c D hc.le hD.le hR


end RiemannResearch.NumberTheory.PrimeNumberTheorem
