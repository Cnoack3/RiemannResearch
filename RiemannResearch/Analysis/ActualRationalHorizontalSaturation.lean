/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualRationalHorizontalEndpoint
import RiemannResearch.Analysis.ArithmeticWeightedFourierEndpoint

/-!
# Saturated actual rational horizontal corrections

Source: Section 6 of `FRZ_Strengthening_2026-11-10.pdf`. The global quartic
bound is proved by combining the actual low-frequency Taylor--Landau estimate
with the global squared-height bound outside that band. Their minimum is the
saturated endpoint envelope. `UniformSelbergDensity (1 / 4)` is retained as
the sole open analytic provider; no horizontal-moment limit is assumed.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The coarse corrected estimate in its unscaled form. -/
theorem eventually_correctedRationalRemainder_quadratic
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ n → 1 ≤ m →
      ‖correctedRationalRemainder T n m‖ ≤
        K * rationalModeWeight n m ^ 2 / Real.log T := by
  obtain ⟨K, hK, hb⟩ := eventually_log_mul_correctedRationalRemainder_le hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with T hT hT1
  intro n m hn hm
  have hL : 0 < Real.log T := Real.log_pos hT1
  have h := hT n m hn hm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL] at h
  exact (le_div_iff₀ hL).2 (by nlinarith)

/-- Global quartic control, including frequencies outside the Landau band.
The large-frequency step is an algebraic consequence of the global quadratic
bound, so it introduces no additional analytic assumption. -/
theorem eventually_correctedRationalRemainder_quartic
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ n → 1 ≤ m →
      ‖correctedRationalRemainder T n m‖ ≤
        K * rationalModeWeight n m ^ 4 / (Real.log T) ^ 3 := by
  obtain ⟨CK, hCK, hcoarse⟩ := eventually_correctedRationalRemainder_quadratic hD
  obtain ⟨CL, hCL, hland⟩ := eventually_rational_landau_error_le_inv_log_cube
  obtain ⟨C, T₀, hC, hT₀, hden⟩ := hD
  let D : ℝ := 32 * C / (3 * (1 / 4 : ℝ) ^ 4)
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  let K : ℝ := D + CL + 64 * CK
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcoarse, hland, eventually_ge_atTop T₀,
    eventually_gt_atTop (1 : ℝ)] with T hcoarse hland hT hT1
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  have hpos (n m : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
      ‖correctedRationalRemainder T n m‖ ≤
        K * rationalModeWeight n m ^ 4 / (Real.log T) ^ 3 := by
    have hn : 1 ≤ n := by omega
    let W := rationalModeWeight n m
    let u := Real.log ((n : ℝ) / (m : ℝ))
    have hW : 1 ≤ W := by
      dsimp [W, rationalModeWeight]
      linarith [abs_nonneg (Real.log (n : ℝ) + Real.log (m : ℝ))]
    have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hlm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    have hlogW : Real.log (n : ℝ) ≤ W := by
      dsimp [W, rationalModeWeight]
      rw [abs_of_nonneg (add_nonneg hln hlm)]
      linarith
    have hu := rational_frequency_bounds hm hmn (le_refl (n : ℝ))
    change 0 < u ∧ u ≤ Real.log (n : ℝ) ∧ _ at hu
    have huW : u ≤ W := hu.2.1.trans hlogW
    have hW2 : 1 ≤ W ^ 2 := by nlinarith
    have hW4 : 1 ≤ W ^ 4 := by nlinarith [sq_nonneg (W ^ 2 - 1)]
    have hu2 : u ^ 2 ≤ W ^ 2 := by nlinarith
    have hu4 : u ^ 4 ≤ W ^ 4 := by
      nlinarith [mul_self_le_mul_self (sq_nonneg u) hu2]
    by_cases hband : W ≤ Real.log T / 8
    · have hE := normalized_horizontalTaylorError_one_of_selberg
        T u C (1 / 4) hT1 hC (by norm_num)
        (by rw [abs_of_pos hu.1]; linarith) (hden T hT)
      change ‖(ordinateSum T u - landauSum T u +
        ((u : ℂ) ^ 2 / 2) * evenHorizontalMoment T u 1) / (T : ℂ)‖ ≤
        D * u ^ 4 / (Real.log T) ^ 3 at hE
      have hLa := hland n m hm hmn (hlogW.trans hband)
      have heq : correctedRationalRemainder T n m =
          (ordinateSum T u - landauSum T u +
            ((u : ℂ) ^ 2 / 2) * evenHorizontalMoment T u 1) / (T : ℂ) +
          (landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ) := by
        have hne : n ≠ m := by omega
        have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT0.ne'
        simp only [correctedRationalRemainder, centeredRationalOrdinate,
          rationalFMZMain, rationalHorizontalCorrection, if_neg hne, if_pos hmn,
          sub_zero, sub_neg_eq_add]
        dsimp [u]
        push_cast
        field_simp
        <;> ring
      rw [heq]
      calc
        _ ≤ ‖(ordinateSum T u - landauSum T u +
              ((u : ℂ) ^ 2 / 2) * evenHorizontalMoment T u 1) / (T : ℂ)‖ +
            ‖(landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)‖ :=
          norm_add_le _ _
        _ ≤ D * u ^ 4 / (Real.log T) ^ 3 + CL / (Real.log T) ^ 3 := add_le_add hE hLa
        _ ≤ K * W ^ 4 / (Real.log T) ^ 3 := by
          rw [← add_div]
          apply div_le_div_of_nonneg_right _ (by positivity)
          have h1 := mul_le_mul_of_nonneg_left hu4 hD0
          have h2 := mul_le_mul_of_nonneg_left hW4 hCL.le
          have h3 : 0 ≤ 64 * CK * W ^ 4 := by positivity
          dsimp [K]
          nlinarith
    · have hLW : Real.log T ≤ 8 * W := by linarith
      have hL2 : (Real.log T) ^ 2 ≤ 64 * W ^ 2 := by
        nlinarith [mul_self_le_mul_self hL.le hLW]
      calc
        _ ≤ CK * W ^ 2 / Real.log T := hcoarse n m hn hm
        _ = (CK * W ^ 2 * (Real.log T) ^ 2) / (Real.log T) ^ 3 := by field_simp
        _ ≤ K * W ^ 4 / (Real.log T) ^ 3 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have h1 := mul_le_mul_of_nonneg_left hL2
            (show 0 ≤ CK * W ^ 2 by positivity)
          have h2 : 0 ≤ (D + CL) * W ^ 4 := by positivity
          dsimp [K]
          nlinarith
  intro n m hn hm
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · exact hpos n m hm hmn
  · subst n
    rw [correctedRationalRemainder_self T m hm, norm_zero]
    positivity
  · rw [correctedRationalRemainder_swap T n m hn hm, norm_star]
    simpa only [rationalModeWeight, add_comm] using hpos m n hn hnm

/-- A single saturated envelope simultaneously yields the fixed A₂ endpoint
and all intermediate A_s estimates. -/
theorem eventually_correctedRationalRemainder_saturated
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ n → 1 ≤ m →
      ‖correctedRationalRemainder T n m‖ ≤
        (K * rationalModeWeight n m ^ 2 / Real.log T) *
          min 1 (rationalModeWeight n m ^ 2 / (Real.log T) ^ 2) := by
  obtain ⟨K₂, hK₂, h₂⟩ := eventually_correctedRationalRemainder_quadratic hD
  obtain ⟨K₄, hK₄, h₄⟩ := eventually_correctedRationalRemainder_quartic hD
  refine ⟨K₂ + K₄, by positivity, ?_⟩
  filter_upwards [h₂, h₄, eventually_gt_atTop (1 : ℝ)] with T h₂ h₄ hT
  intro n m hn hm
  have hL : 0 < Real.log T := Real.log_pos hT
  apply Fourier.norm_le_saturated_of_two_bounds _ _ _ _ (by positivity) hL
  · exact (h₂ n m hn hm).trans (by
      apply div_le_div_of_nonneg_right _ hL.le
      nlinarith [mul_nonneg hK₄.le (sq_nonneg (rationalModeWeight n m))])
  · exact (h₄ n m hn hm).trans (by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg hK₂.le (show 0 ≤ rationalModeWeight n m ^ 4 by positivity)])

end RiemannResearch.Analysis.ActualZeroOrdinate
