/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualRationalHigherHorizontalSaturation
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Fixed weighted-Wiener endpoints at every retained horizontal order

Source: Section 6 of `FRZ_Strengthening_2026-11-10.pdf`. For each fixed
retained order r=J+1, the actual corrected Fourier remainder is
little-oh(T/(log T)^(2r−1)) under the endpoint W_(2r) summability condition.
No convergence of an individual horizontal moment is assumed.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

theorem eventually_scaled_higherCorrectedRationalRemainder_le
    (J : ℕ) (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ n → 1 ≤ m →
      ‖(Real.log T : ℂ) ^ (2 * J + 1) * higherCorrectedRationalRemainder T n m (J + 1)‖ ≤
        K * rationalModeWeight n m ^ (2 * (J + 1)) := by
  obtain ⟨K, hK, hb⟩ := eventually_higherCorrectedRationalRemainder_ratio_coarse J hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with T hT hT1
  intro n m hn hm
  have hL : 0 < Real.log T := Real.log_pos hT1
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  calc
    _ ≤ (Real.log T) ^ (2 * J + 1) *
        (K * Real.log T * (rationalModeWeight n m / Real.log T) ^ (2 * (J + 1))) :=
      mul_le_mul_of_nonneg_left (hT n m hn hm) (by positivity)
    _ = _ := by
      rw [show 2 * (J + 1) = 2 * J + 1 + 1 by omega]
      simp only [div_pow, pow_succ]
      field_simp
      <;> ring

/-- Fixed-mode convergence at the (2r−1)-st logarithmic scale follows from
the global next-even-power bound. -/
theorem tendsto_scaled_higherCorrectedRationalRemainder
    (J : ℕ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ => (Real.log T : ℂ) ^ (2 * J + 1) *
      higherCorrectedRationalRemainder T n m (J + 1)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := eventually_higherCorrectedRationalRemainder_ratio_fine J hD
  have hinv : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hlim := (hinv.pow 2).const_mul (K * rationalModeWeight n m ^ (2 * (J + 2)))
  simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with T hT hT1
  have hL : 0 < Real.log T := Real.log_pos hT1
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  calc
    _ ≤ (Real.log T) ^ (2 * J + 1) *
        (K * Real.log T * (rationalModeWeight n m / Real.log T) ^ (2 * (J + 2))) :=
      mul_le_mul_of_nonneg_left (hT n m hn hm) (by positivity)
    _ = _ := by
      rw [show 2 * (J + 2) = (2 * J + 1) + 3 by omega]
      simp only [div_pow, pow_add, pow_succ, pow_zero, mul_one]
      field_simp
      <;> ring

/-- The endpoint W_(2r) Fourier theorem for every fixed retained order r.
This is an actual-zero application, conditional only on the named Selberg
provider. The order J is fixed before the limiting height is chosen. -/
theorem tendsto_higherCorrectedRationalFourier_endpoint {ι : Type*}
    (J : ℕ) (c : ι → ℂ) (n m : ι → ℕ)
    (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i)
    (hc : Summable (fun i => ‖c i‖ * rationalModeWeight (n i) (m i) ^ (2 * (J + 1))))
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ => (Real.log T : ℂ) ^ (2 * J + 1) *
      ∑' i, c i * higherCorrectedRationalRemainder T (n i) (m i) (J + 1))
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := eventually_scaled_higherCorrectedRationalRemainder_le J hD
  have hpt : ∀ i, Tendsto (fun T : ℝ => c i *
      ((Real.log T : ℂ) ^ (2 * J + 1) *
        higherCorrectedRationalRemainder T (n i) (m i) (J + 1))) atTop (𝓝 0) := by
    intro i
    simpa only [mul_zero] using
      (tendsto_scaled_higherCorrectedRationalRemainder J (hn i) (hm i) hD).const_mul (c i)
  have hdom : ∀ᶠ T : ℝ in atTop, ∀ i,
      ‖c i * ((Real.log T : ℂ) ^ (2 * J + 1) *
        higherCorrectedRationalRemainder T (n i) (m i) (J + 1))‖ ≤
        K * (‖c i‖ * rationalModeWeight (n i) (m i) ^ (2 * (J + 1))) := by
    filter_upwards [hb] with T hT
    intro i
    rw [norm_mul]
    calc
      _ ≤ ‖c i‖ * (K * rationalModeWeight (n i) (m i) ^ (2 * (J + 1))) :=
        mul_le_mul_of_nonneg_left (hT _ _ (hn i) (hm i)) (norm_nonneg _)
      _ = _ := by ring
  have h := tendsto_tsum_of_dominated_convergence (hc.mul_left K) hpt hdom
  simp only [tsum_zero] at h
  convert h using 1
  funext T
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  ring

/-- The full saturated Fourier envelope at every fixed retained order. All
coefficients and rational modes are quantified after the common height
threshold, so the estimate also applies to moving tests. -/
theorem eventually_higherCorrectedRationalFourier_saturated {ι : Type*}
    (J : ℕ) (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (c : ι → ℂ) (n m : ι → ℕ),
      (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ m i) →
      Summable (fun i => ‖c i‖ * rationalModeWeight (n i) (m i) ^ (2 * (J + 1))) →
      ‖(Real.log T : ℂ) ^ (2 * J + 1) *
        ∑' i, c i * higherCorrectedRationalRemainder T (n i) (m i) (J + 1)‖ ≤
      K * ∑' i, ‖c i‖ * rationalModeWeight (n i) (m i) ^ (2 * (J + 1)) *
        min 1 ((rationalModeWeight (n i) (m i) / Real.log T) ^ 2) := by
  obtain ⟨K, hK, hb⟩ := eventually_higherCorrectedRationalRemainder_saturated J hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with T hT hT1
  intro c n m hn hm hc
  have hL : 0 < Real.log T := Real.log_pos hT1
  let w := fun i => rationalModeWeight (n i) (m i)
  let a := fun i => min 1 ((w i / Real.log T) ^ 2)
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    dsimp [w, rationalModeWeight]
    positivity
  have ha0 : ∀ i, 0 ≤ a i := by intro i; dsimp [a]; positivity
  have ha1 : ∀ i, a i ≤ 1 := fun i => min_le_left _ _
  have hsum : Summable (fun i => ‖c i‖ * (w i ^ (2 * (J + 1)) * a i)) := by
    apply hc.of_norm_bounded
    intro i
    have hwi := hw i
    have hai := ha0 i
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hh := mul_le_mul_of_nonneg_left (ha1 i)
      (show 0 ≤ ‖c i‖ * w i ^ (2 * (J + 1)) by positivity)
    change ‖c i‖ * (w i ^ (2 * (J + 1)) * a i) ≤ ‖c i‖ * w i ^ (2 * (J + 1))
    nlinarith
  let e := fun i => (Real.log T : ℂ) ^ (2 * J + 1) *
    higherCorrectedRationalRemainder T (n i) (m i) (J + 1)
  have he : ∀ i, ‖e i‖ ≤ (K / 1) * (w i ^ (2 * (J + 1)) * a i) := by
    intro i
    dsimp [e]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, div_one]
    calc
      _ ≤ (Real.log T) ^ (2 * J + 1) *
          ((K * Real.log T * (w i / Real.log T) ^ (2 * (J + 1))) * a i) :=
        mul_le_mul_of_nonneg_left (hT (n i) (m i) (hn i) (hm i)) (by positivity)
      _ = _ := by
        rw [show 2 * (J + 1) = 2 * J + 1 + 1 by omega]
        simp only [div_pow, pow_succ]
        field_simp
        <;> ring
  have hh := Fourier.weightedFourierRemainder_norm_le c e
    (fun i => w i ^ (2 * (J + 1)) * a i) K 1 hsum he
  simp only [div_one, Fourier.weightedFourierMass] at hh
  have hpair : (∑' i, c i * e i) = (Real.log T : ℂ) ^ (2 * J + 1) *
      ∑' i, c i * higherCorrectedRationalRemainder T (n i) (m i) (J + 1) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro i
    dsimp [e]
    ring
  rw [hpair] at hh
  simpa only [w, a, mul_assoc] using hh

end RiemannResearch.Analysis.ActualZeroOrdinate
