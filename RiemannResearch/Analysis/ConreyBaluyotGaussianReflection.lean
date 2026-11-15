/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotGaussianMoment
import RiemannResearch.Analysis.ConreyBaluyotMellinContour
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Reflection and the initial Gaussian contour for the actual mollifier

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Section 3.3, p. 116, the original-line integral immediately before (3.3.6):
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The reference supports the reflected-product identity and contour strategy.

The existing Mellin weight reality theorem supplies real coefficients for
positive y and positive indices. No nonzero normalizing denominator is
needed for these algebraic identities. The exact cutoff is retained.

The whole initial Gaussian integral is identified with an analytic reflected
product on its original vertical line. This is not the shifted formula:
contour movement, signed residues and horizontal limits remain open.
Integrability on l >= 1/4, l != 1 is already proved in the moment module.
-/

noncomputable section
open Complex MeasureTheory
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.ConreyBaluyot

theorem conj_mollifierCoefficient (σ : ℝ) {y : ℝ} (hy : 0 < y)
    {n : ℕ} (hn : 0 < n) :
    conj (mollifierCoefficient σ y n) = mollifierCoefficient σ y n := by
  have hw : conj (weight σ y) = weight σ y :=
    Complex.conj_eq_iff_im.mpr (weight_im_eq_zero hy)
  have hw' : conj (weight σ (y / n)) = weight σ (y / n) :=
    Complex.conj_eq_iff_im.mpr (weight_im_eq_zero (div_pos hy (by exact_mod_cast hn)))
  simp [mollifierCoefficient, hw, hw']

theorem conj_nonstandardMollifier (σ ε : ℝ) {y : ℝ} (hy : 0 < y) (s : ℂ) :
    conj (nonstandardMollifier σ y ε s) = nonstandardMollifier σ y ε (conj s) := by
  unfold nonstandardMollifier
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
  rw [map_div₀, conj_mollifierCoefficient σ hy hn0]
  congr 1
  have hp := Complex.cpow_conj (n : ℂ) s (by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
      Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact Ne.symm Real.pi_ne_zero)
  simpa using hp.symm

theorem conj_mollifiedZeta (σ ε : ℝ) {y : ℝ} (hy : 0 < y) (s : ℂ) :
    conj (mollifiedZeta σ y ε s) = mollifiedZeta σ y ε (conj s) := by
  simp only [mollifiedZeta, map_mul, ← riemannZeta_conj,
    conj_nonstandardMollifier σ ε hy]

/-- The actual positive norm square is an exact reflected analytic product. -/
theorem mollifiedZeta_vertical_norm_sq_eq_reflected (σ ε l t : ℝ) {y : ℝ}
    (hy : 0 < y) :
    ((‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) =
      mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I) *
        mollifiedZeta σ y ε ((2 * l : ℝ) - ((l : ℂ) + (t : ℂ) * I)) := by
  have hs : conj ((l : ℂ) + (t : ℂ) * I) =
      (2 * l : ℝ) - ((l : ℂ) + (t : ℂ) * I) := by
    simp
    ring
  rw [← hs, ← conj_mollifiedZeta σ ε hy, Complex.mul_conj, Complex.normSq_eq_norm_sq]

def mollifiedGaussianContourKernel (σ y ε l Δ u : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((s - (l : ℂ) - I * u) ^ 2 / (Δ : ℂ) ^ 2) *
    mollifiedZeta σ y ε s * mollifiedZeta σ y ε ((2 * l : ℝ) - s)

/-- Pointwise equality on the original vertical line, before any contour shift. -/
theorem mollifiedGaussianContourKernel_onLine (σ ε l Δ u t : ℝ) {y : ℝ}
    (hy : 0 < y) :
    mollifiedGaussianContourKernel σ y ε l Δ u ((l : ℂ) + (t : ℂ) * I) =
      ((Real.exp (-((t - u) / Δ) ^ 2) *
        ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) := by
  have he : (((l : ℂ) + (t : ℂ) * I) - (l : ℂ) - I * u) ^ 2 / (Δ : ℂ) ^ 2 =
      ((-((t - u) / Δ) ^ 2 : ℝ) : ℂ) := by
    rw [show ((l : ℂ) + (t : ℂ) * I) - (l : ℂ) - I * u =
      ((t : ℂ) - u) * I by ring, mul_pow, Complex.I_sq]
    push_cast
    ring
  unfold mollifiedGaussianContourKernel
  rw [he, ← Complex.ofReal_exp, mul_assoc,
    ← mollifiedZeta_vertical_norm_sq_eq_reflected σ ε l t hy, Complex.ofReal_mul]

/-- Exact initial vertical-contour representation of the actual smoothed moment.
The parameterization uses dt; the i from ds cancels the source's 1/i factor. -/
theorem mollifiedGaussianMoment_eq_vertical_integral (σ ε l : ℝ) {y Δ : ℝ}
    (hy : 0 < y) (hΔ : 0 < Δ) (u : ℝ) :
    (mollifiedGaussianMoment σ y ε l Δ u : ℂ) =
      ((1 / (Δ * Real.sqrt Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, mollifiedGaussianContourKernel σ y ε l Δ u
          ((l : ℂ) + (t : ℂ) * I) := by
  rw [mollifiedGaussianMoment_eq_integral σ y ε l hΔ u, Complex.ofReal_mul]
  congr 1
  calc
    _ = ∫ t : ℝ, ((Real.exp (-((t - u) / Δ) ^ 2) *
        ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) :=
      integral_ofReal.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact (mollifiedGaussianContourKernel_onLine σ ε l Δ u t hy).symm

/-- The original-line contour integral is genuinely integrable away from the pole. -/
theorem integrable_mollifiedGaussianContourKernel (σ ε : ℝ) {y l Δ : ℝ}
    (hy : 0 < y) (hl : 1 / 4 ≤ l) (hl1 : l ≠ 1) (hΔ : 0 < Δ) (u : ℝ) :
    Integrable (fun t : ℝ => mollifiedGaussianContourKernel σ y ε l Δ u
      ((l : ℂ) + (t : ℂ) * I)) := by
  have hi : Integrable (fun t : ℝ => ((Δ * Real.sqrt Real.pi *
      (Real.gaussianDensity (1 / Δ ^ 2) (t - u) *
        ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ^ 2) : ℝ) : ℂ)) :=
    ((integrable_mollifiedGaussianMoment σ y ε hl hl1 hΔ u).const_mul
      (Δ * Real.sqrt Real.pi)).ofReal
  convert hi using 1
  funext t
  rw [mollifiedGaussianContourKernel_onLine σ ε l Δ u t hy,
    Real.gaussianDensity_inv_sq hΔ]
  congr 1
  field_simp [hΔ.ne', ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)]

end RiemannResearch.Analysis.ConreyBaluyot
