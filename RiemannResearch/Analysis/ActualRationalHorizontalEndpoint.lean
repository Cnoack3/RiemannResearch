/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualRationalThirdCoefficient
import RiemannResearch.Analysis.ActualRationalFMZRate
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The fixed squared-height endpoint after retaining horizontal energy

Source: Sections 6--7 of `FRZ_Strengthening_2026-11-10.pdf`, especially the
fixed A₂ endpoint. This file assembles the already proved actual-zero
Taylor, rational Landau, and global rational bounds. The only analytic
premise is `UniformSelbergDensity (1 / 4)`, whose provider is still open.
No limit of the horizontal second moment is assumed. The conclusion is a
signed corrected remainder tending to zero at the T/log T scale.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

/-- The second horizontal term, with its sign chosen to cancel the leading
weight-removal error. It vanishes identically on the diagonal. -/
def rationalHorizontalCorrection (T : ℝ) (n m : ℕ) : ℂ :=
  ((Real.log ((n : ℝ) / (m : ℝ)) : ℂ) ^ 2 / 2) *
    (evenHorizontalMoment T (Real.log ((n : ℝ) / (m : ℝ))) 1 / (T : ℂ))

/-- Exact diagonal centering is performed before adding the correction. -/
def correctedRationalRemainder (T : ℝ) (n m : ℕ) : ℂ :=
  centeredRationalOrdinate T n m / (T : ℂ) - rationalFMZMain n m +
    rationalHorizontalCorrection T n m

theorem evenHorizontalMoment_neg (T u : ℝ) (j : ℕ) :
    evenHorizontalMoment T (-u) j = star (evenHorizontalMoment T u j) := by
  simp [evenHorizontalMoment, sum, phase_neg]

theorem correctedRationalRemainder_self (T : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    correctedRationalRemainder T n n = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp [correctedRationalRemainder, centeredRationalOrdinate, rationalFMZMain,
    rationalHorizontalCorrection, hn0]

theorem rational_log_abs_le_weight (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    |Real.log ((n : ℝ) / (m : ℝ))| ≤ rationalModeWeight n m := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  rw [Real.log_div hn0 hm0, rationalModeWeight,
    abs_of_nonneg (add_nonneg hln hlm)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem correctedRationalRemainder_swap (T : ℝ) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    correctedRationalRemainder T n m = star (correctedRationalRemainder T m n) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hl : Real.log ((n : ℝ) / (m : ℝ)) =
      -Real.log ((m : ℝ) / (n : ℝ)) := by
    rw [Real.log_div hn0 hm0, Real.log_div hm0 hn0]
    ring
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hne : n ≠ m := by omega
    have hne' : m ≠ n := Ne.symm hne
    simp [correctedRationalRemainder, centeredRationalOrdinate,
      rationalFMZMain, rationalHorizontalCorrection, hmn, not_lt_of_ge hmn.le, hne, hne',
      hl, ordinateSum_neg, evenHorizontalMoment_neg]
  · subst n
    simp [correctedRationalRemainder_self T m hm]
  · have hne : n ≠ m := by omega
    have hne' : m ≠ n := Ne.symm hne
    simp [correctedRationalRemainder, centeredRationalOrdinate,
      rationalFMZMain, rationalHorizontalCorrection, hnm, not_lt_of_ge hnm.le, hne, hne',
      hl, ordinateSum_neg, evenHorizontalMoment_neg]

/-- A fixed positive rational mode has a vanishing corrected third-scale
remainder, without requiring convergence of its second horizontal moment. -/
theorem tendsto_log_mul_correctedRationalRemainder_pos {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m < n) (a : ℝ) (ha : 0 < a)
    (hD : UniformSelbergDensity a) :
    Tendsto (fun T : ℝ => (Real.log T : ℂ) * correctedRationalRemainder T n m)
      atTop (𝓝 0) := by
  have hE := tendsto_log_mul_horizontalTaylorError
    (Real.log ((n : ℝ) / (m : ℝ))) a ha hD
  have hL := tendsto_log_mul_rational_landau_error hm hmn
  have h := hE.add hL
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hne : n ≠ m := by omega
  simp only [correctedRationalRemainder, centeredRationalOrdinate,
    rationalFMZMain, rationalHorizontalCorrection, if_neg hne, if_pos hmn,
    sub_zero, sub_neg_eq_add, horizontalTaylorError_one]
  push_cast
  field_simp
  <;> ring

/-- All positive rational numerator/denominator pairs, including the exact
zero mode and the conjugate negative modes. -/
theorem tendsto_log_mul_correctedRationalRemainder {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (a : ℝ) (ha : 0 < a)
    (hD : UniformSelbergDensity a) :
    Tendsto (fun T : ℝ => (Real.log T : ℂ) * correctedRationalRemainder T n m)
      atTop (𝓝 0) := by
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · exact tendsto_log_mul_correctedRationalRemainder_pos hm hmn a ha hD
  · subst n
    simpa only [correctedRationalRemainder_self _ _ hm, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
  · have h := (tendsto_log_mul_correctedRationalRemainder_pos hn hnm a ha hD).star
    simpa only [star_zero, star_mul, Complex.star_def, Complex.conj_ofReal,
      ← correctedRationalRemainder_swap _ _ _ hn hm, mul_comm] using h

/-- The correction itself has a uniform squared arithmetic-height majorant. -/
theorem log_mul_rationalHorizontalCorrection_le
    (T C a : ℝ) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hD : SelbergDensityBound T C a) :
    ‖(Real.log T : ℂ) * rationalHorizontalCorrection T n m‖ ≤
      (2 * C / a ^ 2) * rationalModeWeight n m ^ 2 := by
  let u := Real.log ((n : ℝ) / (m : ℝ))
  have hb := normalized_evenHorizontalMoment_one_le T u C a hT hC ha hD
  have hu := rational_log_abs_le_weight n m hn hm
  have hw : 0 ≤ rationalModeWeight n m := by
    dsimp [rationalModeWeight]
    positivity
  have hu2 : u ^ 2 ≤ rationalModeWeight n m ^ 2 := by
    dsimp [u]
    nlinarith [sq_abs (Real.log ((n : ℝ) / (m : ℝ))), abs_nonneg (Real.log ((n : ℝ) / (m : ℝ)))]
  have heq : (Real.log T : ℂ) * rationalHorizontalCorrection T n m =
      ((u : ℂ) ^ 2 / 2) * ((Real.log T : ℂ) *
        (evenHorizontalMoment T u 1 / (T : ℂ))) := by
    dsimp [rationalHorizontalCorrection, u]
    ring
  rw [heq, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  calc
    _ ≤ (u ^ 2 / 2) * (4 * C / a ^ 2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (rationalModeWeight n m ^ 2 / 2) * (4 * C / a ^ 2) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hu2 (by norm_num))
        (by positivity)
    _ = _ := by ring

/-- One majorant valid for every rational mode at every sufficiently large
height. Constants precede the frequencies. -/
theorem eventually_log_mul_correctedRationalRemainder_le
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ n → 1 ≤ m →
      ‖(Real.log T : ℂ) * correctedRationalRemainder T n m‖ ≤
        K * rationalModeWeight n m ^ 2 := by
  obtain ⟨K, hK, hb⟩ := eventually_centeredRationalOrdinate_remainder_rate hD
  obtain ⟨C, T₀, hC, hT₀, hden⟩ := hD
  refine ⟨K + 32 * C, by positivity, ?_⟩
  filter_upwards [hb, eventually_ge_atTop T₀, eventually_gt_atTop (1 : ℝ)]
    with T hbound hT hT1
  intro n m hn hm
  have hL : 0 < Real.log T := Real.log_pos hT1
  have hc := log_mul_rationalHorizontalCorrection_le T C (1 / 4) n m hn hm
    hT1 hC (by norm_num) (hden T hT)
  have hconstant : 2 * C / (1 / 4 : ℝ) ^ 2 = 32 * C := by ring
  rw [hconstant] at hc
  have hr : ‖(Real.log T : ℂ) *
      (centeredRationalOrdinate T n m / (T : ℂ) - rationalFMZMain n m)‖ ≤
      K * rationalModeWeight n m ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    calc
      _ ≤ Real.log T * ((K / Real.log T) * rationalModeWeight n m ^ 2) :=
        mul_le_mul_of_nonneg_left (hbound n m hn hm) hL.le
      _ = _ := by field_simp
  unfold correctedRationalRemainder
  rw [mul_add]
  exact (norm_add_le _ _).trans (by nlinarith [hr, hc])

/-- Fixed A₂ coefficients attain a little-oh remainder at the third scale.
No uniform little-oh assertion on the whole A₂ unit ball is made. -/
theorem tendsto_correctedRationalFourier_endpoint {ι : Type*}
    (c : ι → ℂ) (n m : ι → ℕ) (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i)
    (hc : Summable (fun i => ‖c i‖ * rationalModeWeight (n i) (m i) ^ 2))
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ => (Real.log T : ℂ) *
      ∑' i, c i * correctedRationalRemainder T (n i) (m i)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := eventually_log_mul_correctedRationalRemainder_le hD
  have hpt : ∀ i, Tendsto (fun T : ℝ => c i *
      ((Real.log T : ℂ) * correctedRationalRemainder T (n i) (m i))) atTop (𝓝 0) := by
    intro i
    simpa only [mul_zero] using
      (tendsto_log_mul_correctedRationalRemainder (hn i) (hm i) (1 / 4)
        (by norm_num) hD).const_mul (c i)
  have hdom : ∀ᶠ T : ℝ in atTop, ∀ i,
      ‖c i * ((Real.log T : ℂ) * correctedRationalRemainder T (n i) (m i))‖ ≤
        K * (‖c i‖ * rationalModeWeight (n i) (m i) ^ 2) := by
    filter_upwards [hb] with T hT
    intro i
    rw [norm_mul]
    calc
      _ ≤ ‖c i‖ * (K * rationalModeWeight (n i) (m i) ^ 2) :=
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

end RiemannResearch.Analysis.ActualZeroOrdinate
