/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualRationalThirdCoefficient

/-!
# Arbitrarily high fixed inverse-logarithmic Landau precision

Source: the proof strategy in Sections 6 and 8 of
`FRZ_Strengthening_2026-11-10.pdf`, using the project's unconditional uniform
rational Landau estimate. Every fixed inverse power of log T is obtained in
the same logarithmic frequency band. Constants and thresholds may depend on
the power; no uniformity for a growing Taylor order is asserted.
-/

noncomputable section
open Filter Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate

theorem log_pow_landau_envelope_tendsto_zero (q : ℕ) :
    Tendsto (fun T : ℝ => (Real.log T) ^ q *
      (Real.exp (Real.log T / 2) *
        (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) / T)) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun T : ℝ => Real.log T / 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_atTop.1 Real.tendsto_log_atTop) (2 * b)] with T hT
    linarith
  have h0 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero q).comp hhalf).const_mul
    ((2 : ℝ) ^ q)
  have h1 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (q + 1)).comp hhalf).const_mul
    (4 * (2 : ℝ) ^ q)
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (q + 2)).comp hhalf).const_mul
    (16 * (2 : ℝ) ^ q)
  have h := (h0.add h1).add h2
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [Function.comp_def, pow_add, pow_one]
  have he : Real.exp (Real.log T / 2) / T = Real.exp (-(Real.log T / 2)) := by
    calc
      _ = Real.exp (Real.log T / 2) / Real.exp (Real.log T) := by rw [Real.exp_log hT]
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  have hp : (2 : ℝ) ^ q * (Real.log T / 2) ^ q = (Real.log T) ^ q := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    _ = ((Real.log T) ^ q * (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T)) *
        (Real.exp (Real.log T / 2) / T) := by
      rw [he, ← hp]
      ring
    _ = _ := by ring

/-- Every fixed inverse-logarithmic power is available throughout the same
rational Landau band, with no Selberg or RH premise. -/
theorem eventually_rational_landau_error_le_inv_log_pow (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ m → m < n → Real.log (n : ℝ) ≤ Real.log T / 8 →
      ‖(landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
        ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)‖ ≤ C / (Real.log T) ^ q := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_rational_landau_rpow_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (9 : ℝ),
    (log_pow_landau_envelope_tendsto_zero q).eventually_le_const (by norm_num : (0 : ℝ) < 1)]
    with T hT henv
  intro n m hm hmn hn
  have hT0 : 0 < T := by linarith
  have hLp : 0 < Real.log T := Real.log_pos (by linarith)
  have hL : 0 ≤ Real.log T := hLp.le
  have hn0 : (0 : ℝ) < n := by
    have hnpos : 0 < n := by omega
    exact_mod_cast hnpos
  let X := Real.exp (Real.log T / 8)
  have hX : 0 < X := Real.exp_pos _
  have hnX : (n : ℝ) ≤ X := by
    rw [← Real.exp_log hn0]
    exact Real.exp_le_exp.mpr hn
  have hp (r : ℝ) (hr : r ≤ 4) : X ^ r ≤ Real.exp (Real.log T / 2) := by
    rw [Real.rpow_def_of_pos hX]
    dsimp [X]
    rw [Real.log_exp]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hXhalf : X ≤ Real.exp (Real.log T / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hlog : Real.log (T + 3) ≤ 2 * Real.log T := by
    calc
      _ ≤ Real.log (T * T) := Real.log_le_log (by linarith) (by nlinarith)
      _ = _ := by rw [Real.log_mul hT0.ne' hT0.ne']; ring
  have hlog0 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hsq : (Real.log (T + 3)) ^ 2 ≤ 4 * (Real.log T) ^ 2 := by
    nlinarith
  have hterms : X ^ (5 / 2 : ℝ) + X ^ (3 / 2 : ℝ) * (Real.log (T + 3)) ^ 2 +
      X * Real.log (T + 3) ≤
      Real.exp (Real.log T / 2) * (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) := by
    have h1 := hp (5 / 2) (by norm_num)
    have h2 := mul_le_mul (hp (3 / 2) (by norm_num)) hsq
      (sq_nonneg _) (Real.exp_pos _).le
    have h3 := mul_le_mul hXhalf hlog hlog0 (Real.exp_pos _).le
    nlinarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  calc
    _ ≤ C * (X ^ (5 / 2 : ℝ) + X ^ (3 / 2 : ℝ) * (Real.log (T + 3)) ^ 2 +
      X * Real.log (T + 3)) / T :=
      div_le_div_of_nonneg_right (hb T X n m hT hm hmn hnX) hT0.le
    _ ≤ C * (Real.exp (Real.log T / 2) *
      (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) / T) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hterms hC.le) hT0.le
    _ ≤ C / (Real.log T) ^ q := by
      have hs : Real.exp (Real.log T / 2) *
          (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) / T ≤ 1 / (Real.log T) ^ q :=
        (le_div_iff₀ (pow_pos hLp q)).2 (by nlinarith [henv])
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hs hC.le

end RiemannResearch.Analysis.ActualZeroOrdinate
