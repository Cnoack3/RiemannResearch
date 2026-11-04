/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Decide
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

/-!
# Exact finite data for the primorial block 2 -> 6

The finite table, the rational head and the rational tail majorant are checked
by kernel arithmetic. `energy_lt_of_complete_tail_bound` is deliberately a
conditional consumer: its premise must bound the COMPLETE unnormalized series.
The separate research note proves that analytic bound by the integral test (or
equivalently telescoping domination). This module does not silently assert that
the finite head itself is the complete energy.
-/
namespace RiemannResearch.RH.QPrimeBlockCertificates
open scoped BigOperators

def residualQ (n : ℕ) : ℚ :=
  1 - ((n % 2 : ℕ) : ℚ) / 2 - ((n % 3 : ℕ) : ℚ) / 3 -
    (2 / 3 : ℚ) * (((n % 6 : ℕ) : ℚ) / 6)

def residualTable : ℕ → ℚ
  | 0 => 1
  | 1 => 1 / 18
  | 2 => 1 / 9
  | 3 => 1 / 6
  | 4 => 2 / 9
  | 5 => -13 / 18
  | _ => 0

theorem residualQ_periodic (n : ℕ) : residualQ n = residualQ (n % 6) := by
  have h2 : (n % 6) % 2 = n % 2 := by omega
  have h3 : (n % 6) % 3 = n % 3 := by omega
  simp only [residualQ, h2, h3, Nat.mod_mod]

theorem residualQ_table : ∀ r : Fin 6, residualQ r.val = residualTable r.val := by
  decide +kernel

def headQ : ℚ :=
  ∑ k ∈ Finset.range 12, residualQ (k + 1) ^ 2 / (((k + 1 : ℕ) : ℚ) ^ 2)

def tailMajorantQ : ℚ :=
  ∑ r ∈ Finset.range 6, residualQ (r + 1) ^ 2 /
    ((6 : ℚ) * (((r + 1 : ℕ) : ℚ) + 6))

def zetaLowerQ : ℚ := 1 + 1 / 4 + 1 / 9 + 1 / 4

theorem rational_certificate :
    headQ = 507158173 / 6915585600 ∧
    tailMajorantQ = 35117 / 1496880 ∧
    zetaLowerQ = 29 / 18 ∧
    (headQ + tailMajorantQ) / zetaLowerQ = 669398713 / 11141776800 ∧
    (headQ + tailMajorantQ) / zetaLowerQ < 1 / 16 ∧
    (3 / 4 : ℚ) < 1 - 4 * ((headQ + tailMajorantQ) / zetaLowerQ) := by
  decide +kernel

/-- This explicitly requires a full-series upper bound, not just a head sum. -/
theorem energy_lt_of_complete_tail_bound (E U z : ℝ)
    (hE : E ≤ U / z)
    (hU : U ≤ (507158173 : ℝ) / 6915585600 + 35117 / 1496880)
    (hz : (29 / 18 : ℝ) ≤ z) : E < (1 / 16 : ℝ) := by
  have hzpos : 0 < z := by linarith
  have hratio : U / z < (1 / 16 : ℝ) := by
    apply (div_lt_iff₀ hzpos).2
    nlinarith
  exact lt_of_le_of_lt hE hratio

theorem relative_gain_gt_three_quarters (E U z : ℝ)
    (hE : E ≤ U / z)
    (hU : U ≤ (507158173 : ℝ) / 6915585600 + 35117 / 1496880)
    (hz : (29 / 18 : ℝ) ≤ z) : (3 / 4 : ℝ) < 1 - E / (1 / 4 : ℝ) := by
  have h := energy_lt_of_complete_tail_bound E U z hE hU hz
  norm_num at h ⊢
  linarith

def residualThirtyQ (n : ℕ) : ℚ :=
  1 - ((n % 2 : ℕ) : ℚ) / 2 - ((n % 3 : ℕ) : ℚ) / 3 -
    (4 / 5 : ℚ) * (((n % 5 : ℕ) : ℚ) / 5) +
    (1 / 5 : ℚ) * (((n % 6 : ℕ) : ℚ) / 6) -
    (1 / 5 : ℚ) * (((n % 15 : ℕ) : ℚ) / 15) -
    (1 / 5 : ℚ) * (((n % 30 : ℕ) : ℚ) / 30)

def upperThirtyQ : ℚ :=
  (18 / 29 : ℚ) * ∑ k ∈ Finset.range 30,
    residualThirtyQ (k + 1) ^ 2 *
      (1 / (((k + 1 : ℕ) : ℚ) ^ 2) + 1 / (30 * ((k + 1 : ℕ) : ℚ)))

def dualDenominatorQ : ℚ :=
  (1 / 4 : ℚ) * (49 / 50 + 64 / 17 + 81 / 10 + 400 / 29) + 3025 / 146

def lowerSixQ : ℚ := (1 / 36 : ℚ) + (3 / 5 : ℚ) / dualDenominatorQ

theorem second_rational_certificate :
    dualDenominatorQ = 98532953 / 3598900 ∧
    (3 / 64 : ℚ) < lowerSixQ ∧
    upperThirtyQ < (1 / 32 : ℚ) ∧
    (1 / 3 : ℚ) < 1 - upperThirtyQ / lowerSixQ := by
  decide +kernel

/-- The actual complete old/new energy bounds must be supplied at application. -/
theorem next_gain_gt_third_of_complete_bounds (Eold Enew : ℝ)
    (hold : (3 / 64 : ℝ) < Eold) (hnew : Enew < (1 / 32 : ℝ)) :
    (1 / 3 : ℝ) < 1 - Enew / Eold := by
  have hp : 0 < Eold := by linarith
  have hr : Enew / Eold < (2 / 3 : ℝ) := by
    apply (div_lt_iff₀ hp).2
    nlinarith
  linarith

end RiemannResearch.RH.QPrimeBlockCertificates
