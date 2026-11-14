/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ComplexMellinExponential
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellinKernel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The actual complex Mellin representation of the damped Estermann series

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
equation (3.1.8) and the first step of the proof of Lemma 3.1.3, pp. 96–97:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The source supports the statement and Mellin strategy.

The initial representation holds for every complex pair of shifts, any residue
modulo a positive modulus, and every positive abscissa putting both shifted
exponents in the absolute-convergence half-plane. Complex exponential inversion
and the integral–double-series exchange are proved in the imported modules.
There is no hypothesis supplying the desired identity or its integrability.

This does not yet shift the contour across the poles or prove the density bound.
-/

open Complex MeasureTheory
open scoped BigOperators
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Absolute integrability of the actual continued Estermann Mellin kernel. -/
theorem integrable_estermannMellinKernel_vertical {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) {lam : ℂ} (hlam : 0 < lam.re) {c : ℝ} (hc : 0 < c)
    (hα : 1 < c + α.re) (hβ : 1 < c + β.re) :
    Integrable (fun t : ℝ => estermannMellinKernel h α β lam ((c : ℂ) + I * t)) := by
  exact integrable_mul_estermann_vertical h α β hα hβ
    (Complex.integrable_gamma_mul_cpow_neg hlam hc)

/-- An explicit integrable majorant for the full Estermann kernel. -/
theorem norm_estermannMellinKernel_vertical_le {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) {lam : ℂ} (hlam : 0 < lam.re) {c : ℝ} (hc : 0 < c)
    (hα : 1 < c + α.re) (hβ : 1 < c + β.re) (t : ℝ) :
    ‖estermannMellinKernel h α β lam ((c : ℂ) + I * t)‖ ≤
      ((‖lam‖ ^ 2 * ((1 / lam.re) ^ (c + 2) * Real.Gamma (c + 2))) /
        (c ^ 2 + t ^ 2)) *
      ∑' p : ℕ × ℕ, ‖estermannTerm h ((c : ℂ) + α) ((c : ℂ) + β) p‖ := by
  unfold estermannMellinKernel
  rw [norm_mul]
  exact mul_le_mul (Complex.gamma_mul_cpow_neg_vertical_bound hlam hc t)
    (norm_estermann_vertical_le h α β hα hβ t) (norm_nonneg _) (by positivity)

/-- The complex Mellin formula for the actual damped series, with all providers discharged. -/
theorem estermannDampedSeries_eq_mellinIntegral {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) {w : ℂ} (hw : 0 < w.im) {c : ℝ} (hc : 0 < c)
    (hα : 1 < c + α.re) (hβ : 1 < c + β.re) :
    estermannDampedSeries h α β w = (1 / (2 * (Real.pi : ℂ))) *
      ∫ t : ℝ, estermannMellinKernel h α β (-2 * (Real.pi : ℂ) * I * w)
        ((c : ℂ) + I * t) := by
  have hlam : 0 < (-2 * (Real.pi : ℂ) * I * w).re := by
    have he : (-2 * (Real.pi : ℂ) * I * w).re = 2 * Real.pi * w.im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [he]
    positivity
  apply estermannDampedSeries_eq_integral_of_inversion h α β w hα hβ
    (Complex.integrable_gamma_mul_cpow_neg hlam hc)
  intro x hx
  have hi := Complex.exponential_eq_mellin_integral hlam hc hx
  convert hi using 1
  congr 1
  ring

end RiemannResearch.Analysis.ConreyBaluyot
