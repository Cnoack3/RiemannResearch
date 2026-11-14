/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gamma bounds for Mellin smoothing

The integral estimate and exact two-step recurrence implement the Gamma
step in Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Lemma 3.1.1, equations (3.1.4) and the bound following it:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

This source supports the proof strategy. The explicit Cauchy-kernel
majorant below is obtained directly from the Gamma integral and recurrence.
No Stirling asymptotic, zeta estimate, or density hypothesis is assumed.
-/

noncomputable section
open Complex MeasureTheory Set

namespace Complex

/-- The Euler Gamma integral gives a bound independent of the imaginary part. -/
theorem gamma_norm_le_real_part {s : ℂ} (hs : 0 < s.re) :
    ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, Real.Gamma_eq_integral hs]
  unfold GammaIntegral
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp

/-- Exact two-step recurrence; no remainder is discarded. -/
theorem gamma_add_three_eq (s : ℂ) (hs : 0 ≤ s.re) :
    Gamma (s + 3) = (s + 2) * (s + 1) * Gamma (s + 1) := by
  have h1 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : s + 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  calc
    _ = (s + 2) * Gamma (s + 2) := by
      convert Gamma_add_one (s + 2) h2 using 1; congr 1; ring
    _ = (s + 2) * ((s + 1) * Gamma (s + 1)) := by
      congr 1
      convert Gamma_add_one (s + 1) h1 using 1; congr 1; ring
    _ = _ := by ring

/-- An integrable vertical majorant, uniform for every nonnegative abscissa. -/
theorem gamma_vertical_cauchy_bound {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    ‖Gamma ((r : ℂ) + I * t + 1)‖ ≤ Real.Gamma (r + 3) / (1 + t ^ 2) := by
  let z : ℂ := (r : ℂ) + I * t
  have hz : 0 ≤ z.re := by simpa [z] using hr
  have he := congrArg norm (gamma_add_three_eq z hz)
  rw [norm_mul, norm_mul] at he
  have hA : 1 + t ^ 2 ≤ ‖z + 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [z]
    nlinarith
  have hB : 1 + t ^ 2 ≤ ‖z + 2‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [z]
    nlinarith
  have hD : 0 < 1 + t ^ 2 := by positivity
  have hAB : 1 + t ^ 2 ≤ ‖z + 2‖ * ‖z + 1‖ := by
    have hp := mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)
    have hA' := mul_le_mul_of_nonneg_right hA hD.le
    have hB' := mul_le_mul_of_nonneg_right hB hD.le
    have hn : 0 ≤ ‖z + 2‖ * ‖z + 1‖ := by positivity
    nlinarith [sq_nonneg (‖z + 2‖ * ‖z + 1‖ - (1 + t ^ 2))]
  have hg : ‖Gamma (z + 3)‖ ≤ Real.Gamma (r + 3) := by
    have h := gamma_norm_le_real_part (s := z + 3) (by simp [z]; linarith)
    simpa [z] using h
  apply (le_div_iff₀ hD).mpr
  change ‖Gamma (z + 1)‖ * (1 + t ^ 2) ≤ _
  calc
    _ ≤ ‖Gamma (z + 1)‖ * (‖z + 2‖ * ‖z + 1‖) :=
      mul_le_mul_of_nonneg_left hAB (norm_nonneg _)
    _ = ‖Gamma (z + 3)‖ := by rw [he]; ring
    _ ≤ _ := hg

end Complex
