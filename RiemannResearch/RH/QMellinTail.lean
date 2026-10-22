/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QMellinTransfer
import RiemannResearch.RH.ParetoMellinTail
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Quantitative complete-Q Mellin tail obstruction

Source: user-provided TwoStageSieveObstructionResearch20261020.md.
The full metric correction is retained before estimating. Exact head
matching and a Mellin discrepancy give quantitative complete-Q energy bounds.
-/

noncomputable section

namespace RiemannResearch.RH.QMellinTransfer
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric

/-- The exact complete-Q metric correction is retained in the localized estimate. -/
theorem qMellin_norm_sq_le_of_head_zero_exact
    (f : QHilbert) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (H : ℕ) (hH : 1 ≤ H) (hhead : ∀ n ≤ H, qSequence f n = 0) :
    ‖qMellin f s‖ ^ 2 ≤
      (zetaTwo * ‖f‖ ^ 2 - metricCorrection f) *
        ((H : ℝ) ^ (1 - 2 * s.re) / (2 * s.re - 1)) := by
  have h := paretoMellin_norm_sq_le_of_head_zero (toPareto f) s hs H hH (by
    simpa only [toPareto_sequence] using hhead)
  rw [norm_identity]
  simpa only [add_sub_cancel_right, qMellin] using h

/-- Uniform quantitative complete-Q Mellin tail estimate. -/
theorem qMellin_norm_sq_le_of_head_zero
    (f : QHilbert) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (H : ℕ) (hH : 1 ≤ H) (hhead : ∀ n ≤ H, qSequence f n = 0) :
    ‖qMellin f s‖ ^ 2 ≤
      zetaTwo * ‖f‖ ^ 2 *
        ((H : ℝ) ^ (1 - 2 * s.re) / (2 * s.re - 1)) := by
  have hd : 0 < 2 * s.re - 1 := by linarith
  apply (qMellin_norm_sq_le_of_head_zero_exact f s hs H hH hhead).trans
  exact mul_le_mul_of_nonneg_right
    (sub_le_self _ (metricCorrection_nonneg f)) (by positivity)

/-- The report's normalization `Phi_sigma = sigma * Mellin`, with its exact constant. -/
theorem normalized_qMellin_norm_sq_le_of_head_zero
    (f : QHilbert) (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ)
    (H : ℕ) (hH : 1 ≤ H) (hhead : ∀ n ≤ H, qSequence f n = 0) :
    ‖(σ : ℂ) * qMellin f (σ : ℂ)‖ ^ 2 ≤
      ‖f‖ ^ 2 * (zetaTwo * σ ^ 2 / (2 * σ - 1)) * (H : ℝ) ^ (1 - 2 * σ) := by
  have h := qMellin_norm_sq_le_of_head_zero f (σ : ℂ) (by simpa using hσ) H hH hhead
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg σ)
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    σ ^ 2 * ‖qMellin f (σ : ℂ)‖ ^ 2 ≤
        σ ^ 2 * (zetaTwo * ‖f‖ ^ 2 *
          ((H : ℝ) ^ (1 - 2 * (σ : ℂ).re) / (2 * (σ : ℂ).re - 1))) := hm
    _ = _ := by simp only [Complex.ofReal_re]; ring

end RiemannResearch.RH.QMellinTransfer

namespace RiemannResearch.RH.QMellinTransfer
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric

/-- Inversion of the complete-Q tail estimate, with the power of the head cutoff explicit. -/
theorem normalized_qMellin_head_zero_energy_lower
    (f : QHilbert) (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ)
    (H : ℕ) (hH : 1 ≤ H) (hhead : ∀ n ≤ H, qSequence f n = 0) :
    ((2 * σ - 1) / (zetaTwo * σ ^ 2)) * (H : ℝ) ^ (2 * σ - 1) *
      ‖(σ : ℂ) * qMellin f (σ : ℂ)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have hZ : 0 < zetaTwo := zetaTwo_pos
  have hd : 0 < 2 * σ - 1 := by linarith
  have hs0 : σ ≠ 0 := by linarith
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hpow : (H : ℝ) ^ (2 * σ - 1) * (H : ℝ) ^ (1 - 2 * σ) = 1 := by
    rw [← Real.rpow_add hHR, show (2 * σ - 1) + (1 - 2 * σ) = 0 by ring,
      Real.rpow_zero]
  have h := normalized_qMellin_norm_sq_le_of_head_zero f σ hσ H hH hhead
  calc
    _ ≤ (((2 * σ - 1) / (zetaTwo * σ ^ 2)) * (H : ℝ) ^ (2 * σ - 1)) *
        (‖f‖ ^ 2 * (zetaTwo * σ ^ 2 / (2 * σ - 1)) * (H : ℝ) ^ (1 - 2 * σ)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = ‖f‖ ^ 2 * ((H : ℝ) ^ (2 * σ - 1) * (H : ℝ) ^ (1 - 2 * σ)) *
        (((2 * σ - 1) / (zetaTwo * σ ^ 2)) * (zetaTwo * σ ^ 2 / (2 * σ - 1))) := by
      ring
    _ = ‖f‖ ^ 2 := by
      rw [hpow]
      field_simp [ne_of_gt zetaTwo_pos, hs0, ne_of_gt hd]

/-- Exact-head interpolation pays the square of its remaining Mellin discrepancy. -/
theorem qMellin_head_match_energy_lower
    (v target : QHilbert) (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ)
    (H : ℕ) (hH : 1 ≤ H)
    (hhead : ∀ n ≤ H, qSequence v n = qSequence target n)
    (hgap : ‖(σ : ℂ) * qMellin v (σ : ℂ)‖ ≤
      ‖(σ : ℂ) * qMellin target (σ : ℂ)‖) :
    ((2 * σ - 1) / (zetaTwo * σ ^ 2)) * (H : ℝ) ^ (2 * σ - 1) *
      (‖(σ : ℂ) * qMellin target (σ : ℂ)‖ -
        ‖(σ : ℂ) * qMellin v (σ : ℂ)‖) ^ 2 ≤ ‖v - target‖ ^ 2 := by
  have hZ : 0 < zetaTwo := zetaTwo_pos
  have hd : 0 < 2 * σ - 1 := by linarith
  have hhead' : ∀ n ≤ H, qSequence (v - target) n = 0 := by
    intro n hn
    change qSequenceLinear (v - target) n = 0
    simp only [map_sub, Pi.sub_apply]
    exact sub_eq_zero.mpr (hhead n hn)
  have he : (σ : ℂ) * qMellin (v - target) (σ : ℂ) =
      (σ : ℂ) * qMellin v (σ : ℂ) - (σ : ℂ) * qMellin target (σ : ℂ) := by
    change (σ : ℂ) * qMellinContinuous (σ : ℂ) (by simpa using hσ) (v - target) = _
    rw [map_sub, mul_sub]
    rfl
  have hsig : ‖(σ : ℂ) * qMellin target (σ : ℂ)‖ -
      ‖(σ : ℂ) * qMellin v (σ : ℂ)‖ ≤
      ‖(σ : ℂ) * qMellin (v - target) (σ : ℂ)‖ := by
    rw [he, norm_sub_rev]
    exact norm_sub_norm_le _ _
  have hsq := pow_le_pow_left₀ (sub_nonneg.mpr hgap) hsig 2
  have hcoef : 0 ≤ ((2 * σ - 1) / (zetaTwo * σ ^ 2)) *
      (H : ℝ) ^ (2 * σ - 1) := by positivity
  exact (mul_le_mul_of_nonneg_left hsq hcoef).trans
    (normalized_qMellin_head_zero_energy_lower (v - target) σ hσ H hH hhead')

/-- The eventual half-signature bound gives exactly the constant in the obstruction report. -/
theorem qMellin_head_match_half_signature_lower
    (v target : QHilbert) (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ)
    (H : ℕ) (hH : 1 ≤ H)
    (hhead : ∀ n ≤ H, qSequence v n = qSequence target n)
    (hsmall : ‖(σ : ℂ) * qMellin v (σ : ℂ)‖ ≤
      ‖(σ : ℂ) * qMellin target (σ : ℂ)‖ / 2) :
    ((2 * σ - 1) * ‖(σ : ℂ) * qMellin target (σ : ℂ)‖ ^ 2 /
      (4 * zetaTwo * σ ^ 2)) * (H : ℝ) ^ (2 * σ - 1) ≤ ‖v - target‖ ^ 2 := by
  have hZ : 0 < zetaTwo := zetaTwo_pos
  have hd : 0 < 2 * σ - 1 := by linarith
  have hnonneg := norm_nonneg ((σ : ℂ) * qMellin target (σ : ℂ))
  have hgap : ‖(σ : ℂ) * qMellin v (σ : ℂ)‖ ≤
      ‖(σ : ℂ) * qMellin target (σ : ℂ)‖ := by linarith
  have hhalf : ‖(σ : ℂ) * qMellin target (σ : ℂ)‖ / 2 ≤
      ‖(σ : ℂ) * qMellin target (σ : ℂ)‖ -
        ‖(σ : ℂ) * qMellin v (σ : ℂ)‖ := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤
    ‖(σ : ℂ) * qMellin target (σ : ℂ)‖ / 2) hhalf 2
  calc
    _ = (((2 * σ - 1) / (zetaTwo * σ ^ 2)) * (H : ℝ) ^ (2 * σ - 1)) *
        (‖(σ : ℂ) * qMellin target (σ : ℂ)‖ / 2) ^ 2 := by ring
    _ ≤ (((2 * σ - 1) / (zetaTwo * σ ^ 2)) * (H : ℝ) ^ (2 * σ - 1)) *
        (‖(σ : ℂ) * qMellin target (σ : ℂ)‖ -
          ‖(σ : ℂ) * qMellin v (σ : ℂ)‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ ≤ ‖v - target‖ ^ 2 := qMellin_head_match_energy_lower v target σ hσ H hH hhead hgap

end RiemannResearch.RH.QMellinTransfer
