/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.QMellinTail
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact logarithmic-target Mellin constants and energy lower bounds

Source: user-provided TwoStageSieveObstructionResearch20261020.md.
The target signature and positive lower constant are unconditional.
The small-transform condition is explicit in the generic head-matching bound.
-/

noncomputable section

namespace RiemannResearch.RH.PrimePowerTarget
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QMellinTransfer

/-- The real normalized signature is exactly the positive geometric-series constant. -/
theorem qTarget_normalized_mellin_norm
    (p : ℕ) (hp : 1 < p) (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) :
    ‖(σ : ℂ) * qMellin (qTarget p hp) (σ : ℂ)‖ =
      1 / ((p : ℝ) ^ σ - 1) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hpow : 1 < (p : ℝ) ^ σ := Real.one_lt_rpow hpR (by linarith)
  have hpowC : (p : ℂ) ^ (σ : ℂ) = (((p : ℝ) ^ σ : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_cpow (show (0 : ℝ) ≤ p by positivity) σ).symm
  have hden : (p : ℂ) ^ (σ : ℂ) - 1 = (((p : ℝ) ^ σ - 1 : ℝ) : ℂ) := by
    rw [hpowC, Complex.ofReal_sub, Complex.ofReal_one]
  rw [qMellin, toPareto_qTarget,
    paretoTarget_mellin_exact p hp (σ : ℂ) (by simpa using hσ),
    hden, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr hpow)]

theorem qTarget_normalized_mellin_norm_pos
    (p : ℕ) (hp : 1 < p) (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) :
    0 < ‖(σ : ℂ) * qMellin (qTarget p hp) (σ : ℂ)‖ := by
  rw [qTarget_normalized_mellin_norm p hp σ hσ]
  apply one_div_pos.mpr
  apply sub_pos.mpr
  exact Real.one_lt_rpow (by exact_mod_cast hp) (by linarith)

/-- The complete-Q lower constant specialized to the actual logarithmic target.
The small-Mellin hypothesis is explicit; a sieve-uniform provider is separate. -/
theorem qTarget_head_match_quantitative_lower
    (p : ℕ) (hp : 1 < p) (v : QHilbert)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (H : ℕ) (hH : 1 ≤ H)
    (hhead : ∀ n ≤ H, qSequence v n = (Nat.log p n : ℝ))
    (hsmall : ‖(σ : ℂ) * qMellin v (σ : ℂ)‖ ≤
      1 / (2 * ((p : ℝ) ^ σ - 1))) :
    ((2 * σ - 1) / (4 * zetaTwo * σ ^ 2 * ((p : ℝ) ^ σ - 1) ^ 2)) *
      (H : ℝ) ^ (2 * σ - 1) ≤ ‖v - qTarget p hp‖ ^ 2 := by
  have hhead' : ∀ n ≤ H, qSequence v n = qSequence (qTarget p hp) n := by
    simpa only [qTarget_sequence] using hhead
  have hsmall' : ‖(σ : ℂ) * qMellin v (σ : ℂ)‖ ≤
      ‖(σ : ℂ) * qMellin (qTarget p hp) (σ : ℂ)‖ / 2 := by
    rw [qTarget_normalized_mellin_norm p hp σ hσ]
    simpa only [div_div, mul_comm ((p : ℝ) ^ σ - 1) 2] using hsmall
  have hl := qMellin_head_match_half_signature_lower v (qTarget p hp) σ hσ H hH
    hhead' hsmall'
  rw [qTarget_normalized_mellin_norm p hp σ hσ] at hl
  simpa only [div_pow, one_pow, mul_one_div, div_div,
    mul_comm (((p : ℝ) ^ σ - 1) ^ 2) (4 * zetaTwo * σ ^ 2)] using hl

theorem qTarget_obstruction_constant_pos
    (p : ℕ) (hp : 1 < p) (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) :
    0 < (2 * σ - 1) / (4 * zetaTwo * σ ^ 2 * ((p : ℝ) ^ σ - 1) ^ 2) := by
  have hZ : 0 < zetaTwo := zetaTwo_pos
  have hd : 0 < 2 * σ - 1 := by linarith
  have hσpos : 0 < σ := by linarith
  have hpow : 0 < (p : ℝ) ^ σ - 1 := sub_pos.mpr
    (Real.one_lt_rpow (by exact_mod_cast hp) hσpos)
  positivity

end RiemannResearch.RH.PrimePowerTarget
