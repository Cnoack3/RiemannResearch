/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualRationalFMZLimits
import RiemannResearch.Analysis.ActualZeroCountUpper

/-!
# Uniform rational FMZ domination and infinite Fourier synthesis

The logarithmic rational Landau band is proved unconditionally. Combined with
the explicit Selberg density input and the unconditional total-count upper
bound, it gives one linear log-height majorant for every rational mode.
Dominated convergence then proves weighted absolutely summable Fourier
synthesis with one frequency moment. Selberg remains an explicit, unproved
analytic input.

Source: Ford--Meng--Zaharescu, Theorem 1 and Corollary 1.1,
https://arxiv.org/abs/1511.06814, support the classical target and comparison
strategy. The linear envelope is a refinement of this project's rational
Landau and reflection estimates; no novelty claim is made. Its concrete RH
consumer is signed prime Gram analysis and the full Weil positivity problem,
as explained in RH/FMZStrengtheningWeil20261011.md. This does not prove RH.
-/

noncomputable section
open Filter Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

theorem rationalLandauMain_le_log {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    rationalLandauMain n m ≤ Real.log (n : ℝ) := by
  have hn : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  have hm0 : (0 : ℝ) < m := by positivity
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  rw [rationalLandauMain_eq_vonMangoldt_div_sqrt hm hmn]
  split_ifs with hd
  · have hq : ((n / m : ℕ) : ℝ) = (n : ℝ) / (m : ℝ) := by
      exact Nat.cast_div hd hm0.ne'
    have hratio : 1 ≤ (n : ℝ) / (m : ℝ) := by
      apply (le_div_iff₀ hm0).2
      simpa using (show (m : ℝ) ≤ n by exact_mod_cast hmn.le)
    have hsqrt : 1 ≤ Real.sqrt ((n : ℝ) / (m : ℝ)) :=
      Real.one_le_sqrt.mpr hratio
    have hden : 1 ≤ (2 * Real.pi) * Real.sqrt ((n : ℝ) / (m : ℝ)) := by
      nlinarith [Real.pi_gt_three]
    have hqle : ((n / m : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n m
    have hqpos : (0 : ℝ) < (n / m : ℕ) := by rw [hq]; positivity
    calc
      _ ≤ (ArithmeticFunction.vonMangoldt (n / m) : ℝ) :=
        div_le_self (ArithmeticFunction.vonMangoldt_nonneg) hden
      _ ≤ Real.log ((n / m : ℕ) : ℝ) := ArithmeticFunction.vonMangoldt_le_log
      _ ≤ _ := Real.log_le_log hqpos hqle
  · exact hlog

private theorem half_log_envelope_tendsto_zero :
    Tendsto (fun T : ℝ =>
      Real.exp (Real.log T / 2) *
        (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) / T) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun T : ℝ => Real.log T / 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_atTop.1 Real.tendsto_log_atTop) (2 * b)] with T hT
    linarith
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hhalf
  have h1 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hhalf).const_mul 4
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hhalf).const_mul 16
  have h := (h0.add h2).add h1
  simp only [zero_add, mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [Function.comp_def, pow_zero, one_mul, pow_one]
  have he : Real.exp (Real.log T / 2) / T = Real.exp (-(Real.log T / 2)) := by
    calc
      _ = Real.exp (Real.log T / 2) / Real.exp (Real.log T) := by rw [Real.exp_log hT]
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  calc
    _ = (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) *
        (Real.exp (Real.log T / 2) / T) := by rw [he]; ring
    _ = _ := by ring

/-- Uniform rational Landau remainder control throughout a logarithmic band. -/
theorem eventually_rational_landau_error_le_const :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ m → m < n → Real.log (n : ℝ) ≤ Real.log T / 8 →
      ‖(landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
        ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_rational_landau_rpow_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (9 : ℝ),
    half_log_envelope_tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1)]
    with T hT henv
  intro n m hm hmn hn
  have hT0 : 0 < T := by linarith
  have hL : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
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
    _ ≤ C := by simpa using mul_le_mul_of_nonneg_left henv hC.le

/-- A single polynomial envelope controls all rational modes simultaneously.
The small-band factor `H ^ 2 / log T` is bounded by `H`, retaining the
logarithmic denominator. The only analytic premise is classical Selberg. -/
theorem eventually_rational_ordinate_log_envelope
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ m → m < n →
      ‖ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ)‖ ≤
        K * (1 + Real.log (n : ℝ)) := by
  obtain ⟨CD, TD, hCD, hTD, hden⟩ := hD
  obtain ⟨CL, hCL, hland⟩ := eventually_rational_landau_error_le_const
  obtain ⟨CN, hCN, hcount⟩ := exists_normalized_ordinate_bound
  let D : ℝ := 128 * CD / 3
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D + CL + 1 + 8 * CN, by positivity, ?_⟩
  filter_upwards [hland, eventually_ge_atTop TD, eventually_ge_atTop (9 : ℝ),
    (tendsto_atTop.1 Real.tendsto_log_atTop) 1] with T hland hT hT9 hL1
  intro n m hm hmn
  let H := Real.log (n : ℝ)
  let u := Real.log ((n : ℝ) / (m : ℝ))
  have hT0 : 0 < T := by linarith
  have hT1 : 1 < T := by linarith
  have hn : 1 ≤ n := by omega
  have hH : 0 ≤ H := Real.log_nonneg (by exact_mod_cast hn)
  have hu := rational_frequency_bounds hm hmn (le_refl (n : ℝ))
  change 0 < u ∧ u ≤ H ∧ _ at hu
  by_cases hband : H ≤ Real.log T / 8
  · have herr := normalized_ordinate_landau_error_of_classical_selberg
      T u CD hT1 hCD (by rw [abs_of_pos hu.1]; exact hu.2.1.trans hband) (hden T hT)
    have herr' : ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ ≤ D * H := by
      apply herr.trans
      change D * u ^ 2 / Real.log T ≤ D * H
      apply (div_le_iff₀ (by linarith : 0 < Real.log T)).2
      have hs : u ^ 2 ≤ H ^ 2 := by nlinarith [hu.1, hu.2.1]
      have hHL : H ≤ Real.log T := by linarith
      have hprod : H ^ 2 ≤ H * Real.log T := by
        nlinarith [mul_nonneg hH (sub_nonneg.mpr hHL)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hs.trans hprod) hD0
    have hmain : ‖(rationalLandauMain n m : ℂ)‖ ≤ H := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (rationalLandauMain_nonneg n m)]
      exact rationalLandauMain_le_log hm hmn
    have heq : ordinateSum T u / (T : ℂ) =
        (ordinateSum T u - landauSum T u) / (T : ℂ) +
        (landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ) -
        (rationalLandauMain n m : ℂ) := by
      have hc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT0.ne'
      push_cast
      field_simp [hc]
      ring
    rw [heq]
    have hl := hland n m hm hmn hband
    change ‖(landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ)) /
      (T : ℂ)‖ ≤ CL at hl
    calc
      _ ≤ (‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ +
        ‖(landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)‖) +
        ‖(rationalLandauMain n m : ℂ)‖ := (norm_sub_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ D * H + CL + H := by linarith
      _ ≤ _ := by nlinarith [mul_nonneg hCL.le hH, mul_nonneg hCN.le hH]
  · have hb := hcount T u hT9
    have hLH : Real.log T ≤ 8 * H := by linarith
    calc
      _ ≤ CN * Real.log T := hb
      _ ≤ 8 * CN * H := by nlinarith
      _ ≤ _ := by nlinarith [mul_nonneg hD0 hH, mul_nonneg hCL.le hH]

/-- Symmetric log-height weight for a rational Fourier frequency. -/
def rationalModeWeight (n m : ℕ) : ℝ :=
  1 + |Real.log (n : ℝ) + Real.log (m : ℝ)|

theorem eventually_centeredRationalOrdinate_envelope
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ n → 1 ≤ m →
      ‖centeredRationalOrdinate T n m / (T : ℂ)‖ ≤ K * rationalModeWeight n m := by
  obtain ⟨K, hK, hb⟩ := eventually_rational_ordinate_log_envelope hD
  refine ⟨K, hK, hb.mono ?_⟩
  intro T hT n m hn hm
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hnW : 1 + Real.log (n : ℝ) ≤ rationalModeWeight n m := by
    unfold rationalModeWeight
    rw [abs_of_nonneg (add_nonneg hln hlm)]
    linarith
  have hmW : 1 + Real.log (m : ℝ) ≤ rationalModeWeight n m := by
    unfold rationalModeWeight
    rw [abs_of_nonneg (add_nonneg hln hlm)]
    linarith
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hne : n ≠ m := by omega
    simp only [centeredRationalOrdinate, if_neg hne, sub_zero]
    exact (hT n m hm hmn).trans (mul_le_mul_of_nonneg_left hnW hK.le)
  · subst n
    simp [centeredRationalOrdinate, hm0, rationalModeWeight, hK.le]
    positivity
  · have hne : n ≠ m := by omega
    have hlog : Real.log ((n : ℝ) / (m : ℝ)) =
        -Real.log ((m : ℝ) / (n : ℝ)) := by
      rw [Real.log_div hn0 hm0, Real.log_div hm0 hn0]
      ring
    simp only [centeredRationalOrdinate, if_neg hne, sub_zero, hlog, ordinateSum_neg]
    rw [norm_div, norm_star, ← norm_div]
    exact (hT m n hn hnm).trans (mul_le_mul_of_nonneg_left hmW hK.le)

/-- Infinite Fourier synthesis under the natural weighted absolute-summability
condition. The arithmetic limits and uniform majorant are proved above. -/
theorem tendsto_rational_fourier_series_of_uniformSelberg
    {ι : Type*} (a : ι → ℂ) (n m : ι → ℕ)
    (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i)
    (ha : Summable (fun i => ‖a i‖ * rationalModeWeight (n i) (m i)))
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ => ∑' i, a i *
      (centeredRationalOrdinate T (n i) (m i) / (T : ℂ)))
      atTop (𝓝 (∑' i, a i * rationalFMZMain (n i) (m i))) := by
  obtain ⟨K, hK, hbound⟩ := eventually_centeredRationalOrdinate_envelope hD
  apply tendsto_tsum_of_dominated_convergence (ha.mul_left K)
  · intro i
    exact (tendsto_centeredRationalOrdinate_div_of_uniformSelberg (hn i) (hm i) hD).const_mul (a i)
  · filter_upwards [hbound] with T hT
    intro i
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_left (hT (n i) (m i) (hn i) (hm i)) (norm_nonneg (a i))
    nlinarith

end RiemannResearch.Analysis.ActualZeroOrdinate
