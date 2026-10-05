/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic dimension-weighted Landau error envelopes

The complete three-term fixed-c=2 remainder is transformed exactly to an
exponential envelope. Polynomial-times-exponential decay proves uniform
vanishing at every fixed square-root-log support coefficient. This module
is scalar analysis; ActualLandauOperatorResidual specializes it to actual
zeta zeros with the arithmetic main matrix retained. Source: the proved
ActualUniformRationalLandau provider and the repository support argument.
-/

noncomputable section
open Filter

namespace RiemannResearch.Analysis.LandauGrowth

/-- Complete dimension-weighted fixed-c=2 Landau remainder after the
exponential height factor. Its three summands are retained exactly. -/
def matrixEnvelope (L ell : ℝ) : ℝ :=
  Real.exp (7 * ell / 2 - L) +
    L ^ 2 * Real.exp (5 * ell / 2 - L) +
    L * Real.exp (2 * ell - L)

theorem matrixEnvelope_nonneg {L : ℝ} (hL : 0 ≤ L) (ell : ℝ) :
    0 ≤ matrixEnvelope L ell := by
  unfold matrixEnvelope
  positivity

theorem matrixEnvelope_le {L ell : ℝ} (hL : 0 ≤ L) (hell : ell ≤ L / 8) :
    matrixEnvelope L ell ≤ (1 + L ^ 2 + L) * Real.exp (-L / 2) := by
  have h1 : Real.exp (7 * ell / 2 - L) ≤ Real.exp (-L / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (5 * ell / 2 - L) ≤ Real.exp (-L / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (2 * ell - L) ≤ Real.exp (-L / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold matrixEnvelope
  calc
    _ ≤ Real.exp (-L / 2) + L ^ 2 * Real.exp (-L / 2) +
        L * Real.exp (-L / 2) := add_le_add
      (add_le_add h1 (mul_le_mul_of_nonneg_left h2 (sq_nonneg L)))
      (mul_le_mul_of_nonneg_left h3 hL)
    _ = _ := by ring

theorem polynomial_exp_majorant_tendsto_zero :
    Tendsto (fun L : ℝ => (1 + L ^ 2 + L) * Real.exp (-L / 2))
      atTop (nhds 0) := by
  have hhalf : Tendsto (fun L : ℝ => L / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hhalf
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hhalf
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hhalf
  have h := h0.add ((h2.const_mul 4).add (h1.const_mul 2))
  convert h using 1
  · funext L
    change (1 + L ^ 2 + L) * Real.exp (-L / 2) =
      (L / 2) ^ 0 * Real.exp (-(L / 2)) +
        (4 * ((L / 2) ^ 2 * Real.exp (-(L / 2))) +
          2 * ((L / 2) ^ 1 * Real.exp (-(L / 2))))
    rw [show -(L / 2) = -L / 2 by ring]
    simp only [pow_zero, pow_one, one_mul]
    ring
  · norm_num

/-- No zero-density premise is needed for this deterministic Landau envelope.
An eventual logarithmic support budget supplies a uniform vanishing bound. -/
theorem matrixEnvelope_tendsto_zero (ell : ℝ → ℝ)
    (hell : ∀ᶠ L : ℝ in atTop, ell L ≤ L / 8) :
    Tendsto (fun L : ℝ => matrixEnvelope L (ell L)) atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    exact matrixEnvelope_nonneg hL (ell L)
  · filter_upwards [hell, eventually_ge_atTop (0 : ℝ)] with L he hL
    exact matrixEnvelope_le hL he
  · exact polynomial_exp_majorant_tendsto_zero

theorem sqrt_support_eventually_le (c : ℝ) :
    ∀ᶠ L : ℝ in atTop, c * Real.sqrt L ≤ L / 8 := by
  filter_upwards [eventually_ge_atTop (64 * |c| ^ 2),
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  have hs0 := Real.sqrt_nonneg L
  have hs2 := Real.sq_sqrt hL0
  have hc0 := abs_nonneg c
  have hs : 8 * |c| ≤ Real.sqrt L := by
    by_contra hn
    have hh : Real.sqrt L < 8 * |c| := lt_of_not_ge hn
    have hp := mul_pos (sub_pos.mpr hh)
      (by nlinarith : 0 < 8 * |c| + Real.sqrt L)
    nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hs) hs0
  have hc := mul_le_mul_of_nonneg_right (le_abs_self c) hs0
  nlinarith

theorem matrixEnvelope_sqrt_tendsto_zero (c : ℝ) :
    Tendsto (fun L : ℝ => matrixEnvelope L (c * Real.sqrt L)) atTop (nhds 0) :=
  matrixEnvelope_tendsto_zero _ (sqrt_support_eventually_le c)

theorem matrixEnvelope_mono {L a b : ℝ} (hL : 0 ≤ L) (hab : a ≤ b) :
    matrixEnvelope L a ≤ matrixEnvelope L b := by
  unfold matrixEnvelope
  apply add_le_add
  · apply add_le_add
    · exact Real.exp_le_exp.mpr (by linarith)
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
        (sq_nonneg L)
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hL

theorem mul_rpow_div_eq_exp {Y d : ℝ} (hY : 0 < Y) (hd : 0 < d) (a : ℝ) :
    d * d ^ a / Y = Real.exp ((a + 1) * Real.log d - Real.log Y) := by
  rw [Real.rpow_def_of_pos hd, Real.exp_sub,
    show (a + 1) * Real.log d = Real.log d + Real.log d * a by ring,
    Real.exp_add, Real.exp_log hd, Real.exp_log hY]

/-- Exact change from the three rpow summands to their dimension-weighted
exponential envelope. No summand is removed. -/
theorem matrixEnvelope_eq_rpow {Y d : ℝ} (hY : 0 < Y) (hd : 0 < d) :
    matrixEnvelope (Real.log Y) (Real.log d) =
      d * (d ^ (5 / 2 : ℝ) + d ^ (3 / 2 : ℝ) * (Real.log Y) ^ 2 +
        d * Real.log Y) / Y := by
  have h1 := mul_rpow_div_eq_exp hY hd (5 / 2 : ℝ)
  have h2 := mul_rpow_div_eq_exp hY hd (3 / 2 : ℝ)
  have h3 := mul_rpow_div_eq_exp hY hd (1 : ℝ)
  norm_num at h1 h2 h3
  unfold matrixEnvelope
  rw [show 7 * Real.log d / 2 = (7 / 2 : ℝ) * Real.log d by ring,
    show 5 * Real.log d / 2 = (5 / 2 : ℝ) * Real.log d by ring,
    ← h1, ← h2, ← h3]
  ring

end RiemannResearch.Analysis.LandauGrowth
