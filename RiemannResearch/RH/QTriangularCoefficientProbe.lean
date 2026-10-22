/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/

import RiemannResearch.RH.QTriangularRieszEnergy
import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.RH.MobiusReciprocalChargeBridge
import RiemannResearch.RH.MobiusTriangularCharge
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
/-!
# Exact recovery of coefficients from adjacent triangular averages

Source: user-provided Balazard triangular dual refinement, continued
19 October 2026. Finite summation twice inverts by second differences.
The native-Q probe has exactly the existing coefficient functional as
its Riesz pairing. These probes are dual vectors; no legal membership
or stable synthesis bound is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
theorem triangularChargeRiesz_scaled (N : ℕ) :
    (N : ℝ) • triangularChargeRiesz N =
      ∑ k ∈ Finset.range N, reciprocalChargeRiesz k := by
  by_cases hN : N = 0
  · simp [hN, triangularChargeRiesz]
  · rw [triangularChargeRiesz, smul_smul,
      mul_inv_cancel₀ (show (N : ℝ) ≠ 0 by exact_mod_cast hN), one_smul]
theorem triangularChargeRiesz_first_difference (n : ℕ) :
    (n + 1 : ℝ) • triangularChargeRiesz (n + 1) -
      (n : ℝ) • triangularChargeRiesz n = reciprocalChargeRiesz n := by
  have h := triangularChargeRiesz_scaled (n + 1)
  push_cast at h
  rw [h, triangularChargeRiesz_scaled, Finset.sum_range_succ]
  abel
theorem triangularChargeRiesz_second_difference (n : ℕ) :
    (n + 2 : ℝ) • triangularChargeRiesz (n + 2) -
      (2 : ℝ) • ((n + 1 : ℝ) • triangularChargeRiesz (n + 1)) +
      (n : ℝ) • triangularChargeRiesz n =
        (1 / (n + 1 : ℝ)) • mobiusRieszHilbert (n + 1) := by
  have h1 := triangularChargeRiesz_first_difference n
  have h2 := triangularChargeRiesz_first_difference (n + 1)
  have hr : reciprocalChargeRiesz (n + 1) - reciprocalChargeRiesz n =
      (1 / (n + 1 : ℝ)) • mobiusRieszHilbert (n + 1) := by
    unfold reciprocalChargeRiesz
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    abel
  rw [← hr, ← h1, ← h2]
  push_cast
  module
end RiemannResearch.RH.Pareto
namespace RiemannResearch.RH.QTriangularCharge
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer SquarefreeMobiusProjection
/-- The index n represents coefficient n+1. -/
def coefficientProbe (n : ℕ) : QHilbert :=
  (n + 1 : ℝ) • ((2 : ℝ) • ((n + 1 : ℝ) • riesz (n + 1)) -
    (n : ℝ) • riesz n - (n + 2 : ℝ) • riesz (n + 2))
theorem coefficientProbe_inner (n : ℕ) (h : QHilbert) :
    inner ℝ (coefficientProbe n) h = qCoefficientCLM (n + 1) h := by
  have hh := congrArg (fun z : ThresholdHilbert => inner ℝ z (toPareto h))
    (triangularChargeRiesz_second_difference n)
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
    mobiusRieszHilbert_inner] at hh
  unfold coefficientProbe
  simp only [real_inner_smul_left, inner_sub_left, riesz_inner]
  unfold charge
  change _ = -mobiusDifferenceCLM (n + 1) (toPareto h)
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hn] at hh ⊢
  nlinarith [hh]
theorem coefficientProbe_biorthogonal (i j : ℕ) :
    inner ℝ (coefficientProbe (i + 1)) (qResidue (j + 2)) =
      if i = j then 1 else 0 := by
  rw [coefficientProbe_inner]
  exact q_coordinate_biorthogonal i j
end RiemannResearch.RH.QTriangularCharge
