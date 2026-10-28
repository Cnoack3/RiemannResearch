/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualRationalFMZDomination
import RiemannResearch.Analysis.ActualRationalFMZLimits
import RiemannResearch.Analysis.ActualUniformRationalLandau
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import RiemannResearch.Analysis.ArithmeticWeightedFourierRemainder
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative rational FMZ and moving Fourier tests

The proved rational Landau estimate gives an O(1/log T) normalized error in
its logarithmic band. The classical Selberg comparison and total zero-count
bound extend this to every rational frequency at the cost of the square of
its logarithmic height. Uniformity permits moving Fourier coefficients and
frequencies whenever their squared-height Wiener mass is o(log T).

Source for the comparison target and strategy: Ford--Meng--Zaharescu,
Theorem 1 and Corollary 1.1, https://arxiv.org/abs/1511.06814, and the
user-provided FMZ comparison. The rates here are derived from the project's
existing bounds, rather than assumed from that reference. No novelty claim
is made. The concrete RH consumers are prime-phase test synthesis and signed
Gram analysis; these results do not prove RH.

The Landau rate and arithmetic coefficient bound are unconditional. Every
actual-ordinate rate retains UniformSelbergDensity (1/4) explicitly; its
provider remains open. Exact diagonal centering and negative-frequency
conjugation are preserved before estimating the complete remainder.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

private theorem log_landau_envelope_tendsto_zero :
    Tendsto (fun T : ℝ => Real.log T *
      (Real.exp (Real.log T / 2) *
        (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) / T)) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun T : ℝ => Real.log T / 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_atTop.1 Real.tendsto_log_atTop) (2 * b)] with T hT
    linarith
  have h1 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hhalf).const_mul 2
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hhalf).const_mul 8
  have h3 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp hhalf).const_mul 32
  have h := (h1.add h2).add h3
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [Function.comp_def, pow_one]
  have he : Real.exp (Real.log T / 2) / T = Real.exp (-(Real.log T / 2)) := by
    calc
      _ = Real.exp (Real.log T / 2) / Real.exp (Real.log T) := by rw [Real.exp_log hT]
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  calc
    _ = (Real.log T * (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T)) *
        (Real.exp (Real.log T / 2) / T) := by rw [he]; ring
    _ = _ := by ring

/-- Uniform normalized Landau error O(1/log T) throughout the logarithmic
rational-frequency band. This estimate has no Selberg or RH premise. -/
theorem eventually_rational_landau_error_le_inv_log :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ m → m < n → Real.log (n : ℝ) ≤ Real.log T / 8 →
      ‖(landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
        ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)‖ ≤ C / Real.log T := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_rational_landau_rpow_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (9 : ℝ),
    log_landau_envelope_tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1)]
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
    _ ≤ C / Real.log T := by
      have hs : Real.exp (Real.log T / 2) *
          (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) / T ≤ 1 / Real.log T :=
        (le_div_iff₀ hLp).2 (by nlinarith [henv])
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hs hC.le


/-- Uniform squared-log-height rate for every positive rational frequency.
The only analytic premise is the classical Selberg density estimate. -/
theorem eventually_rational_ordinate_remainder_rate
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ m → m < n →
      ‖ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ) +
        (rationalLandauMain n m : ℂ)‖ ≤
          K * (1 + Real.log (n : ℝ)) ^ 2 / Real.log T := by
  obtain ⟨CD, TD, hCD, hTD, hden⟩ := hD
  obtain ⟨CL, hCL, hland⟩ := eventually_rational_landau_error_le_inv_log
  obtain ⟨CN, hCN, hcount⟩ := exists_normalized_ordinate_bound
  let D : ℝ := 128 * CD / 3
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  let K : ℝ := D + CL + 64 * CN + 8
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hland, eventually_ge_atTop TD, eventually_ge_atTop (9 : ℝ)]
    with T hland hT hT9
  intro n m hm hmn
  let H := Real.log (n : ℝ)
  let u := Real.log ((n : ℝ) / (m : ℝ))
  have hT0 : 0 < T := by linarith
  have hT1 : 1 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  have hn : 1 ≤ n := by omega
  have hH : 0 ≤ H := Real.log_nonneg (by exact_mod_cast hn)
  have hu := rational_frequency_bounds hm hmn (le_refl (n : ℝ))
  change 0 < u ∧ u ≤ H ∧ _ at hu
  have hmain : ‖(rationalLandauMain n m : ℂ)‖ ≤ H := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (rationalLandauMain_nonneg n m)]
    exact rationalLandauMain_le_log hm hmn
  by_cases hband : H ≤ Real.log T / 8
  · have herr := normalized_ordinate_landau_error_of_classical_selberg
      T u CD hT1 hCD (by rw [abs_of_pos hu.1]; exact hu.2.1.trans hband) (hden T hT)
    have hl := hland n m hm hmn hband
    have heq : ordinateSum T u / (T : ℂ) + (rationalLandauMain n m : ℂ) =
        (ordinateSum T u - landauSum T u) / (T : ℂ) +
        (landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ) := by
      have hc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT0.ne'
      push_cast
      field_simp [hc]
      ring
    change ‖ordinateSum T u / (T : ℂ) + (rationalLandauMain n m : ℂ)‖ ≤ _
    rw [heq]
    calc
      _ ≤ ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ +
          ‖(landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)‖ :=
        norm_add_le _ _
      _ ≤ D * u ^ 2 / Real.log T + CL / Real.log T := add_le_add herr hl
      _ ≤ K * (1 + H) ^ 2 / Real.log T := by
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ hL.le
        have hs : u ^ 2 ≤ (1 + H) ^ 2 := by nlinarith [hu.1, hu.2.1]
        have hds := mul_le_mul_of_nonneg_left hs hD0
        have hw : 1 ≤ (1 + H) ^ 2 := by nlinarith [sq_nonneg H]
        have hcw := mul_le_mul_of_nonneg_left hw hCL.le
        have hrest : 0 ≤ (64 * CN + 8) * (1 + H) ^ 2 := by positivity
        dsimp [K]
        nlinarith
  · have hb := hcount T u hT9
    have hLH : Real.log T ≤ 8 * H := by linarith
    have hs : (Real.log T) ^ 2 ≤ 64 * H ^ 2 := by
      nlinarith [mul_self_le_mul_self hL.le hLH]
    have hHL : H * Real.log T ≤ 8 * H ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hLH hH]
    change ‖ordinateSum T u / (T : ℂ) + (rationalLandauMain n m : ℂ)‖ ≤ _
    calc
      _ ≤ ‖ordinateSum T u / (T : ℂ)‖ + ‖(rationalLandauMain n m : ℂ)‖ :=
        norm_add_le _ _
      _ ≤ CN * Real.log T + H := add_le_add hb hmain
      _ ≤ K * (1 + H) ^ 2 / Real.log T := by
        apply (le_div_iff₀ hL).2
        have hcs := mul_le_mul_of_nonneg_left hs hCN.le
        have hw : H ^ 2 ≤ (1 + H) ^ 2 := by nlinarith
        have hrest : 0 ≤ (D + CL) * (1 + H) ^ 2 := by positivity
        have hcw := mul_le_mul_of_nonneg_left hw (show 0 ≤ 64 * CN + 8 by positivity)
        dsimp [K]
        nlinarith

/-- All rational modes, with exact diagonal centering and conjugate modes. -/
theorem eventually_centeredRationalOrdinate_remainder_rate
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ n → 1 ≤ m →
      ‖centeredRationalOrdinate T n m / (T : ℂ) - rationalFMZMain n m‖ ≤
        (K / Real.log T) * rationalModeWeight n m ^ 2 := by
  obtain ⟨K, hK, hb⟩ := eventually_rational_ordinate_remainder_rate hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with T hT hT1
  intro n m hn hm
  have hL : 0 < Real.log T := Real.log_pos hT1
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hw : rationalModeWeight n m = 1 + Real.log (n : ℝ) + Real.log (m : ℝ) := by
    simp only [rationalModeWeight, abs_of_nonneg (add_nonneg hln hlm)]
    ring
  have hbound (a : ℝ) (ha : 0 ≤ a) (haw : a ≤ Real.log n + Real.log m) :
      K * (1 + a) ^ 2 / Real.log T ≤ (K / Real.log T) * rationalModeWeight n m ^ 2 := by
    rw [hw, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hL.le
    apply mul_le_mul_of_nonneg_left _ hK.le
    nlinarith
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hne : n ≠ m := by omega
    simp only [centeredRationalOrdinate, rationalFMZMain, if_pos hmn,
      if_neg hne, sub_zero, sub_neg_eq_add]
    exact (hT n m hm hmn).trans (hbound _ hln (by linarith))
  · subst n
    have hz : centeredRationalOrdinate T m m / (T : ℂ) - rationalFMZMain m m = 0 := by
      simp [centeredRationalOrdinate, rationalFMZMain, hm0]
    rw [hz, norm_zero]
    positivity
  · have hne : n ≠ m := by omega
    have hnot : ¬ m < n := by omega
    have hlog : Real.log ((n : ℝ) / (m : ℝ)) =
        -Real.log ((m : ℝ) / (n : ℝ)) := by
      rw [Real.log_div hn0 hm0, Real.log_div hm0 hn0]
      ring
    have heq : centeredRationalOrdinate T n m / (T : ℂ) - rationalFMZMain n m =
        star (ordinateSum T (Real.log ((m : ℝ) / (n : ℝ))) / (T : ℂ) +
          (rationalLandauMain m n : ℂ)) := by
      simp [centeredRationalOrdinate, rationalFMZMain, hnot, hnm, hne, hlog,
        ordinateSum_neg]
    rw [heq, norm_star]
    exact (hT m n hn hnm).trans (hbound _ hlm (by linarith))

/-- The arithmetic correction has a uniform first-height bound. -/
theorem rationalFMZMain_norm_le_weight (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ‖rationalFMZMain n m‖ ≤ rationalModeWeight n m := by
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hw : rationalModeWeight n m = 1 + Real.log (n : ℝ) + Real.log (m : ℝ) := by
    simp only [rationalModeWeight, abs_of_nonneg (add_nonneg hln hlm)]
    ring
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · simp only [rationalFMZMain, if_pos hmn, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (rationalLandauMain_nonneg n m)]
    rw [hw]
    exact (rationalLandauMain_le_log hm hmn).trans (by linarith)
  · subst n
    have hz : rationalFMZMain m m = 0 := by simp [rationalFMZMain]
    rw [hz, norm_zero, hw]
    positivity
  · have hnot : ¬ m < n := by omega
    simp only [rationalFMZMain, if_neg hnot, if_pos hnm, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (rationalLandauMain_nonneg m n)]
    rw [hw]
    exact (rationalLandauMain_le_log hn hnm).trans (by linarith)

/-- Quantitative infinite rational Fourier synthesis. The constants and
height threshold precede every choice of coefficients and rational modes. -/
theorem eventually_rational_fourier_remainder_bound {ι : Type*}
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (a : ι → ℂ) (n m : ι → ℕ),
      (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ m i) →
      Summable (fun i => ‖a i‖ * rationalModeWeight (n i) (m i) ^ 2) →
      ‖Fourier.weightedFourierPairing a
          (fun i => centeredRationalOrdinate T (n i) (m i) / (T : ℂ)) -
        Fourier.weightedFourierPairing a (fun i => rationalFMZMain (n i) (m i))‖ ≤
        (K / Real.log T) *
          Fourier.weightedFourierMass a (fun i => rationalModeWeight (n i) (m i) ^ 2) := by
  obtain ⟨K, hK, hb⟩ := eventually_centeredRationalOrdinate_remainder_rate hD
  refine ⟨K, hK, hb.mono ?_⟩
  intro T hT a n m hn hm ha
  have hmain : Summable (fun i => a i * rationalFMZMain (n i) (m i)) := by
    apply ha.of_norm_bounded
    intro i
    have hw : 1 ≤ rationalModeWeight (n i) (m i) := by
      unfold rationalModeWeight
      linarith [abs_nonneg (Real.log (n i : ℝ) + Real.log (m i : ℝ))]
    have hsq : rationalModeWeight (n i) (m i) ≤ rationalModeWeight (n i) (m i) ^ 2 := by
      nlinarith
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((rationalFMZMain_norm_le_weight (n i) (m i) (hn i) (hm i)).trans hsq) (norm_nonneg _)
  exact (Fourier.weightedFourierPairing_remainder_bound_of_limit_summable a
    (fun i => centeredRationalOrdinate T (n i) (m i) / (T : ℂ))
    (fun i => rationalFMZMain (n i) (m i))
    (fun i => rationalModeWeight (n i) (m i) ^ 2) K (Real.log T)
    hmain ha (fun i => hT (n i) (m i) (hn i) (hm i))).2

/-- Moving coefficients, changing rational frequencies, and infinitely many
prime coordinates are allowed when their squared-height Wiener mass is
o(log T). This is an actual-zero conclusion, conditional only on Selberg. -/
theorem tendsto_moving_rational_fourier_remainder {ι : Type*}
    (a : ℝ → ι → ℂ) (n m : ℝ → ι → ℕ)
    (hn : ∀ T i, 1 ≤ n T i) (hm : ∀ T i, 1 ≤ m T i)
    (ha : ∀ T, Summable (fun i => ‖a T i‖ * rationalModeWeight (n T i) (m T i) ^ 2))
    (hsmall : Tendsto (fun T : ℝ =>
      Fourier.weightedFourierMass (a T)
        (fun i => rationalModeWeight (n T i) (m T i) ^ 2) / Real.log T) atTop (𝓝 0))
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ =>
      Fourier.weightedFourierPairing (a T)
        (fun i => centeredRationalOrdinate T (n T i) (m T i) / (T : ℂ)) -
      Fourier.weightedFourierPairing (a T)
        (fun i => rationalFMZMain (n T i) (m T i))) atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := eventually_rational_fourier_remainder_bound (ι := ι) hD
  have hlim := hsmall.const_mul K
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hb] with T hT
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using
    hT (a T) (n T) (m T) (hn T) (hm T) (ha T)

end RiemannResearch.Analysis.ActualZeroOrdinate

#print axioms RiemannResearch.Analysis.ActualZeroOrdinate.eventually_centeredRationalOrdinate_remainder_rate
#print axioms RiemannResearch.Analysis.ActualZeroOrdinate.tendsto_moving_rational_fourier_remainder
