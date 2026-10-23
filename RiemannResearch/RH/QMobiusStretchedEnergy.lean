/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusStretchedEnergy
import RiemannResearch.RH.CanonicalMobiusLogEnvelopeEnergy
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.Analysis.StretchedExponentialBounds
import RiemannResearch.RH.QMobiusExactHead
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quantitative complete-Q energy of the Möbius exact heads

Source: continuation of the user-provided uniform dual bound agenda,
22 October 2026. This module transports the existing, unconditional Pareto energy providers to
the actual Q measure. The infinite tail remains included. The resulting upper
bounds still permit unbounded energy and do not assert constant closure.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QMobiusStretchedEnergy

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open RiemannResearch.Analysis

theorem exactHead_eventual_stretched_energy :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖QMobiusExactHead.exactHead N‖ ^ 2 ≤ 6 / zetaTwo + C * (N : ℝ) *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) := by
  have hz : 0 < zetaTwo := zetaTwo_pos
  obtain ⟨a, ha, C, hC, hbounds⟩ := Pareto.canonicalMobius_eventual_stretched_bounds
  refine ⟨a, ha, (2 / zetaTwo) * C, by positivity, ?_⟩
  filter_upwards [hbounds] with N hN
  have he := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
    (QMobiusExactHead.exactHead N)
  rw [QSquarefreeSublinearHeads.toPareto_exactHead] at he
  have hle : ‖QMobiusExactHead.exactHead N‖ ^ 2 ≤
      (2 / zetaTwo) * ‖Pareto.canonicalMobiusHilbert N‖ ^ 2 := by
    calc
      _ ≤ (2 * ‖Pareto.canonicalMobiusHilbert N‖ ^ 2) / zetaTwo :=
        (le_div_iff₀ zetaTwo_pos).mpr (by nlinarith)
      _ = _ := by ring
  calc
    _ ≤ (2 / zetaTwo) * ‖Pareto.canonicalMobiusHilbert N‖ ^ 2 := hle
    _ ≤ (2 / zetaTwo) * (3 + C * (N : ℝ) *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ)))) :=
      mul_le_mul_of_nonneg_left hN.2 (by positivity)
    _ = _ := by ring

theorem exactHead_error_eventual_stretched_energy :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖qOne - QMobiusExactHead.exactHead N‖ ^ 2 ≤ 16 / zetaTwo + C * (N : ℝ) *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) := by
  have hz : 0 < zetaTwo := zetaTwo_pos
  obtain ⟨a, ha, C, hC, hbounds⟩ := Pareto.canonicalMobiusResidual_eventual_stretched_energy
  refine ⟨a, ha, (2 / zetaTwo) * C, by positivity, ?_⟩
  filter_upwards [hbounds] with N hN
  have he := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
    (qOne - QMobiusExactHead.exactHead N)
  have hmap : toPareto (qOne - QMobiusExactHead.exactHead N) =
      Pareto.hilbertOne - Pareto.canonicalMobiusHilbert N := by
    change toParetoLinear (qOne - QMobiusExactHead.exactHead N) = _
    rw [map_sub]
    change toPareto qOne - toPareto (QMobiusExactHead.exactHead N) = _
    rw [toPareto_qOne, QSquarefreeSublinearHeads.toPareto_exactHead]
  rw [hmap] at he
  have hle : ‖qOne - QMobiusExactHead.exactHead N‖ ^ 2 ≤
      (2 / zetaTwo) * ‖Pareto.hilbertOne - Pareto.canonicalMobiusHilbert N‖ ^ 2 := by
    calc
      _ ≤ (2 * ‖Pareto.hilbertOne - Pareto.canonicalMobiusHilbert N‖ ^ 2) / zetaTwo :=
        (le_div_iff₀ zetaTwo_pos).mpr (by nlinarith)
      _ = _ := by ring
  calc
    _ ≤ (2 / zetaTwo) * ‖Pareto.hilbertOne - Pareto.canonicalMobiusHilbert N‖ ^ 2 := hle
    _ ≤ (2 / zetaTwo) * (8 + C * (N : ℝ) *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ)))) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    _ = _ := by ring

/-- A finite, uniform Mertens-tail envelope controls the complete Q energy.
The analytic premise is explicit; it is not a uniform RH-strength bound. -/
theorem exactHead_energy_of_uniform_mertens_log
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hsmall : ε * (1 + Real.log (1 / ε)) ≤ 1 / 2)
    (hM : ∀ y : ℝ, (N : ℝ) ≤ y →
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M y| ≤ ε * y) :
    ‖QMobiusExactHead.exactHead N‖ ^ 2 / (N : ℝ) ≤
      (2 / zetaTwo) * (3 / (N : ℝ) + 260 * (ε * (1 + Real.log (1 / ε)))) := by
  have hz : 0 < zetaTwo := zetaTwo_pos
  have hp := (Pareto.canonicalMobius_energy_of_uniform_mertens_log
    N hN ε hε hεone hsmall hM).2
  have he := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
    (QMobiusExactHead.exactHead N)
  rw [QSquarefreeSublinearHeads.toPareto_exactHead] at he
  have hle : ‖QMobiusExactHead.exactHead N‖ ^ 2 ≤
      (2 / zetaTwo) * ‖Pareto.canonicalMobiusHilbert N‖ ^ 2 := by
    calc
      _ ≤ (2 * ‖Pareto.canonicalMobiusHilbert N‖ ^ 2) / zetaTwo :=
        (le_div_iff₀ zetaTwo_pos).mpr (by nlinarith)
      _ = _ := by ring
  have hd := div_le_div_of_nonneg_right hle (Nat.cast_nonneg N)
  calc
    _ ≤ (2 / zetaTwo) *
        (‖Pareto.canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ)) := by
      simpa only [mul_div_assoc] using hd
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)



open ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis

/-- Every fixed logarithmic saving holds for the complete Q head energy.
The constant may depend on k; this does not imply uniform boundedness. -/
theorem exactHead_eventual_log_power_energy (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖QMobiusExactHead.exactHead N‖ ^ 2 ≤
        6 / zetaTwo + C * (N : ℝ) / (6 + Real.log (N : ℝ)) ^ k := by
  obtain ⟨a, ha, C, hC, hbounds⟩ := exactHead_eventual_stretched_energy
  obtain ⟨B, hB, hpower⟩ := logProductExp_le_inverse_nat_power a (1 / 11) ha
    (by norm_num) k
  refine ⟨C * B, mul_nonneg hC hB, ?_⟩
  filter_upwards [hbounds, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hs : 6 ≤ 6 + Real.log (N : ℝ) := by
    linarith [Real.log_nonneg hNreal]
  have hp := mul_le_mul_of_nonneg_left (hpower _ hs)
    (mul_nonneg hC (Nat.cast_nonneg N))
  calc
    _ ≤ 6 / zetaTwo + C * (N : ℝ) *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) := hN
    _ ≤ 6 / zetaTwo + C * (N : ℝ) *
        (B / (6 + Real.log (N : ℝ)) ^ k) := by linarith only [hp]
    _ = _ := by ring

/-- Every fixed logarithmic saving also holds for the complete error energy. -/
theorem exactHead_error_eventual_log_power_energy (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖qOne - QMobiusExactHead.exactHead N‖ ^ 2 ≤
        16 / zetaTwo + C * (N : ℝ) / (6 + Real.log (N : ℝ)) ^ k := by
  obtain ⟨a, ha, C, hC, hbounds⟩ := exactHead_error_eventual_stretched_energy
  obtain ⟨B, hB, hpower⟩ := logProductExp_le_inverse_nat_power a (1 / 11) ha
    (by norm_num) k
  refine ⟨C * B, mul_nonneg hC hB, ?_⟩
  filter_upwards [hbounds, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hs : 6 ≤ 6 + Real.log (N : ℝ) := by
    linarith [Real.log_nonneg hNreal]
  have hp := mul_le_mul_of_nonneg_left (hpower _ hs)
    (mul_nonneg hC (Nat.cast_nonneg N))
  calc
    _ ≤ 16 / zetaTwo + C * (N : ℝ) *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) := hN
    _ ≤ 16 / zetaTwo + C * (N : ℝ) *
        (B / (6 + Real.log (N : ℝ)) ^ k) := by linarith only [hp]
    _ = _ := by ring


end RiemannResearch.RH.QMobiusStretchedEnergy
