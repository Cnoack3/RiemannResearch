/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Exact vertical Gaussian Laplace transform

The integral is absolutely convergent for every complex frequency and is
independent of the vertical abscissa. The normalization is exactly
Delta * sqrt(pi).

The proof specializes Mathlib's `integral_cexp_quadratic` and
`integrable_cexp_quadratic'` from
`Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`.

Concrete RH-program consumer: evaluation of `gaussianArithmeticTransform`
in `ConreyBaluyotGaussianArithmetic.lean`, after inserting the Euler
integral for Gamma. This inner Gaussian calculation is proved; that
Gamma/Fubini step and the subsequent rotated Estermann identification
are not proved by this module.
-/

noncomputable section
open Complex MeasureTheory
namespace Complex

/-- Absolute convergence for arbitrary complex frequency and every real abscissa. -/
theorem gaussian_vertical_laplace_integrable (c l u : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) (z : ℂ) :
    Integrable (fun t : ℝ =>
      exp ((((c : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2) *
        exp (((c : ℂ) + I * t) * z)) := by
  let a : ℂ := c - l - I * u
  let b : ℂ := -(1 / (Δ : ℂ)^2)
  let B : ℂ := 2 * a * I / (Δ : ℂ)^2 + I * z
  let D : ℂ := a^2 / (Δ : ℂ)^2 + (c : ℂ) * z
  have hb : b.re < 0 := by
    have he : b = ((-(1 / Δ^2) : ℝ) : ℂ) := by dsimp [b]; push_cast; rfl
    rw [he, Complex.ofReal_re]
    exact neg_neg_of_pos (by positivity)
  convert integrable_cexp_quadratic' hb B D using 1
  funext t
  rw [← Complex.exp_add]
  congr 1
  dsimp [b, B, D, a]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  <;> ring

/-- Exact complex Gaussian inversion; the right side is independent of the abscissa c. -/
theorem gaussian_vertical_laplace_integral (c l u : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) (z : ℂ) :
    (∫ t : ℝ,
      exp ((((c : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2) *
        exp (((c : ℂ) + I * t) * z)) =
      ((Δ * Real.sqrt Real.pi : ℝ) : ℂ) *
        exp (((l : ℂ) + I * u) * z - (Δ : ℂ)^2 * z^2 / 4) := by
  let a : ℂ := c - l - I * u
  let b : ℂ := -(1 / (Δ : ℂ)^2)
  let B : ℂ := 2 * a * I / (Δ : ℂ)^2 + I * z
  let D : ℂ := a^2 / (Δ : ℂ)^2 + (c : ℂ) * z
  have hΔc : (Δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΔ.ne'
  have hb : b.re < 0 := by
    have he : b = ((-(1 / Δ^2) : ℝ) : ℂ) := by dsimp [b]; push_cast; rfl
    rw [he, Complex.ofReal_re]
    exact neg_neg_of_pos (by positivity)
  have he : (fun t : ℝ =>
      exp ((((c : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2) *
        exp (((c : ℂ) + I * t) * z)) =
      (fun t : ℝ => exp (b * (t : ℂ)^2 + B * (t : ℂ) + D)) := by
    funext t
    rw [← Complex.exp_add]
    congr 1
    dsimp [b, B, D, a]
    field_simp
    ring_nf
    simp [Complex.I_sq]
    <;> ring
  rw [he, integral_cexp_quadratic hb B D]
  have hp : ((Real.pi : ℂ) / -b) ^ (1 / 2 : ℂ) = ((Δ * Real.sqrt Real.pi : ℝ) : ℂ) := by
    have hbase : (Real.pi : ℂ) / -b = ((Real.pi * Δ^2 : ℝ) : ℂ) := by
      dsimp [b]
      push_cast
      field_simp
    rw [hbase, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (show 0 ≤ Real.pi * Δ^2 by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hΔ.le, mul_comm]
  rw [hp]
  congr 2
  dsimp [D, B, b, a]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  <;> ring

end Complex
