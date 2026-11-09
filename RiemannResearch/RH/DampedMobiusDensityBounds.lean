/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PSeriesTail
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Integral bounds for the actual damped Mobius density

Source: the integral comparison for the zeta p-series in the user-provided
Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf, Theorem 6.2.
The lower and upper series comparisons give an unconditional second-order
bound for the actual reciprocal zeta centering constant.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

/-- The real p-series has the same value as zeta on the real convergence ray. -/
theorem riemannZeta_real_eq_nat_rpow_tsum {x : ℝ} (hx : 1 < x) :
    riemannZeta (x : ℂ) = ((∑' n : ℕ, 1 / (n : ℝ) ^ x : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hx)]
  simp only [Complex.ofReal_tsum, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]

set_option maxHeartbeats 800000 in
-- Integral and shifted infinite-sum elaboration exceeds the default heartbeat budget.
/-- The integral under the decreasing p-series starts at 1 and is 1/ε. -/
theorem one_div_le_zeta_real_series {ε : ℝ} (hε : 0 < ε) :
    1 / ε ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + ε) := by
  have hexp : -(1 + ε) < (-1 : ℝ) := by linarith
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + ε))) :=
    Real.summable_nat_rpow.mpr hexp
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(1 + ε)))
      (Ici ((1 : ℕ) : ℝ)) := by
    intro x hx y _hy hxy
    have hx1 : (1 : ℝ) ≤ x := by simpa only [Set.mem_Ici, Nat.cast_one] using hx
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx1) hxy
      (by linarith only [hε])
  have hi := AntitoneOn.integral_le_tsum_comp_add (1 : ℕ) hanti hs
    (fun x hx => Real.rpow_nonneg (by
      have hx1 : (1 : ℝ) < x := by simpa only [Set.mem_Ioi, Nat.cast_one] using hx
      exact le_trans zero_le_one hx1.le) (-(1 + ε)))
  have hint : (∫ x : ℝ in Ioi (1 : ℝ), x ^ (-(1 + ε))) = 1 / ε := by
    rw [integral_Ioi_rpow_of_lt hexp (by norm_num : (0 : ℝ) < 1)]
    simp only [Real.one_rpow]
    rw [show -(1 + ε) + 1 = -ε by ring]
    exact neg_div_neg_eq 1 ε
  have hzero : (0 : ℝ) ^ (-(1 + ε)) = 0 := Real.zero_rpow (by linarith only [hε])
  have hshift : (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-(1 + ε))) =
      ∑' n : ℕ, (n : ℝ) ^ (-(1 + ε)) := by
    simpa only [Nat.cast_zero, hzero, zero_add] using hs.tsum_eq_zero_add.symm
  simp only [Nat.cast_one] at hi
  rw [hint, hshift] at hi
  simpa only [Real.rpow_neg (Nat.cast_nonneg _), one_div] using hi

/-- Global, unconditional bound for the actual signed Mobius density.
No Hilbert-space membership hypothesis appears here. -/
theorem dampedMobius_density_bounds {ε : ℝ} (hε : 0 < ε) :
    0 ≤ (1 / riemannZeta (1 + (ε : ℂ))).re ∧
      (1 / riemannZeta (1 + (ε : ℂ))).re ≤ ε := by
  let S : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + ε)
  have hlower : 1 / ε ≤ S := one_div_le_zeta_real_series hε
  have hS : 0 < S := lt_of_lt_of_le (by positivity : 0 < 1 / ε) hlower
  have hz : riemannZeta (1 + (ε : ℂ)) = (S : ℂ) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using
      (riemannZeta_real_eq_nat_rpow_tsum (by linarith : 1 < 1 + ε))
  have hreal : (1 / riemannZeta (1 + (ε : ℂ))).re = 1 / S := by
    rw [hz]
    norm_cast
  rw [hreal]
  constructor
  · exact (one_div_pos.mpr hS).le
  · apply (div_le_iff₀ hS).mpr
    have hm : 1 ≤ S * ε := (div_le_iff₀ hε).mp hlower
    simpa only [mul_comm] using hm

/-- Removing the first term leaves a tail bounded by the integral from 1. -/
theorem zeta_real_series_le_one_add_one_div {ε : ℝ} (hε : 0 < ε) :
    (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + ε)) ≤ 1 + 1 / ε := by
  have hexp : -(1 + ε) < (-1 : ℝ) := by linarith
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + ε))) :=
    Real.summable_nat_rpow.mpr hexp
  have hs' : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(1 + ε))) :=
    (summable_nat_add_iff 1).mpr hs
  have hzero : (0 : ℝ) ^ (-(1 + ε)) = 0 := Real.zero_rpow (by linarith)
  have hsplit : (∑' n : ℕ, (n : ℝ) ^ (-(1 + ε))) =
      1 + ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-(1 + ε)) := by
    rw [hs.tsum_eq_zero_add]
    simp only [Nat.cast_zero, hzero, zero_add]
    rw [hs'.tsum_eq_zero_add]
    simp only [zero_add, Nat.cast_one, Real.one_rpow]
  have htail : (∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-(1 + ε))) ≤ 1 / ε := by
    simpa only [Nat.cast_one, Real.one_rpow, add_sub_cancel_left] using
      (Real.tsum_nat_rpow_tail_le (p := 1 + ε) (by linarith)
        (N := 1) (by omega))
  calc
    _ = ∑' n : ℕ, (n : ℝ) ^ (-(1 + ε)) := by
      simp only [Real.rpow_neg (Nat.cast_nonneg _), one_div]
    _ = _ := hsplit
    _ ≤ 1 + 1 / ε := add_le_add le_rfl htail

/-- The complete global integral sandwich for the actual signed density. -/
theorem dampedMobius_density_sandwich {ε : ℝ} (hε : 0 < ε) :
    ε / (1 + ε) ≤ (1 / riemannZeta (1 + (ε : ℂ))).re ∧
      (1 / riemannZeta (1 + (ε : ℂ))).re ≤ ε := by
  let S : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + ε)
  have hlower : 1 / ε ≤ S := one_div_le_zeta_real_series hε
  have hupper : S ≤ 1 + 1 / ε := zeta_real_series_le_one_add_one_div hε
  have hS : 0 < S := lt_of_lt_of_le (by positivity : 0 < 1 / ε) hlower
  have hz : riemannZeta (1 + (ε : ℂ)) = (S : ℂ) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using
      (riemannZeta_real_eq_nat_rpow_tsum (by linarith : 1 < 1 + ε))
  have hreal : (1 / riemannZeta (1 + (ε : ℂ))).re = 1 / S := by
    rw [hz]
    norm_cast
  constructor
  · rw [hreal]
    apply (div_le_div_iff₀ (by linarith : 0 < 1 + ε) hS).mpr
    calc
      ε * S ≤ ε * (1 + 1 / ε) := mul_le_mul_of_nonneg_left hupper hε.le
      _ = 1 * (1 + ε) := by field_simp [ne_of_gt hε]; ring
  · exact (dampedMobius_density_bounds hε).2

/-- A uniform quadratic remainder in the reciprocal zeta density; this
supplies the centering part of the second-order smoothed approximation. -/
theorem dampedMobius_density_sub_epsilon_le_sq {ε : ℝ} (hε : 0 < ε) :
    |(1 / riemannZeta (1 + (ε : ℂ))).re - ε| ≤ ε ^ 2 := by
  obtain ⟨hlower, hupper⟩ := dampedMobius_density_sandwich hε
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  have hm : ε ≤ (1 / riemannZeta (1 + (ε : ℂ))).re * (1 + ε) :=
    (div_le_iff₀ (by linarith : 0 < 1 + ε)).mp hlower
  nlinarith [mul_le_mul_of_nonneg_left hupper hε.le]

end RiemannResearch.RH.Pareto
