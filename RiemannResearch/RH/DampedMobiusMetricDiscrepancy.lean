/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QMetricApproximateHeads
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.DampedMobiusCoefficients
import RiemannResearch.RH.DampedMobiusSeed
import RiemannResearch.RH.DampedMobiusSquarefreeClosure
import RiemannResearch.RH.DampedMobiusSignedGram
import RiemannResearch.RH.ArithmeticFloorHilbertSeries
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Signed finite-head bounds for the actual damped P/Q discrepancy

Source: `BalazardDeRotonResearch20261019.md`, final finite comparison.
The damped approximation family is the one studied by Michel Balazard and
Anne de Roton, "Sur un critère de Báez-Duarte pour l'hypothèse de Riemann",
https://arxiv.org/abs/0812.1689. That reference supports the choice of family;
the discrete charge and metric estimates are derived here from the existing
exact arithmetic and P/Q identities.

The finite bounds are unconditional for nonnegative damping. The signed
endpoint envelope improves the triangle envelope in the research note.
The ratio limit has an explicit relative-head-budget hypothesis; it supplies
no unconditional decay estimate for the full Pareto error and proves no RH.
-/
noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.BalazardDeRoton
open ZetaTwoHilbert QParetoEquivalence DampedMobiusSquarefreeClosure

/-- The reciprocal charge, kept real for physical-coordinate estimates. -/
def realCharge (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N, dampedMobiusWeight ε (m + 1) / ((m + 1 : ℕ) : ℝ)

/-- The first divisor coefficient equals one; the remaining finite prefix
contains exactly the terms at physical sites 2 through n. -/
theorem dampedPrefix_eq_one_add_shifted (ε : ℝ) {n : ℕ} (hn : 0 < n) :
    dampedMobiusPrefix ε n =
      1 + ∑ k ∈ Finset.range (n - 1), dampedDivisorCoefficient ε (k + 2) := by
  rw [dampedMobiusPrefix_eq_sum_divisors]
  change (∑ k ∈ Finset.range (n + 1), dampedDivisorCoefficient ε k) = _
  have hs := Finset.sum_range_add (fun k => dampedDivisorCoefficient ε k) 2 (n - 1)
  have he : 2 + (n - 1) = n + 1 := by omega
  rw [he] at hs
  have hsmall : (∑ k ∈ Finset.range 2, dampedDivisorCoefficient ε k) = 1 := by
    norm_num [Finset.sum_range_succ]
  simpa only [hsmall, Nat.add_comm] using hs

/-- Uniform bound for the positive part of the actual divisor prefix.
No RH or infinite-energy hypothesis occurs. -/
theorem dampedPrefix_sub_one_bounds {ε : ℝ} (hε : 0 ≤ ε)
    {n H : ℕ} (hn : 0 < n) (hnH : n ≤ H) :
    0 ≤ dampedMobiusPrefix ε n - 1 ∧
      dampedMobiusPrefix ε n - 1 ≤ (n : ℝ) * (ε * Real.log H) := by
  rw [dampedPrefix_eq_one_add_shifted ε hn]
  simp only [add_sub_cancel_left]
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
  have hB : 0 ≤ ε * Real.log H := mul_nonneg hε (Real.log_nonneg hH)
  constructor
  · exact Finset.sum_nonneg (fun k _ => dampedDivisorCoefficient_nonneg hε _)
  · calc
      (∑ k ∈ Finset.range (n - 1), dampedDivisorCoefficient ε (k + 2))
          ≤ ∑ _k ∈ Finset.range (n - 1), ε * Real.log H := by
        apply Finset.sum_le_sum
        intro k hk
        have hkH : k + 2 ≤ H := by have := Finset.mem_range.mp hk; omega
        exact (dampedDivisorCoefficient_le_mul_log hε (by omega : 2 ≤ k + 2)).trans
          (mul_le_mul_of_nonneg_left
            (Real.log_le_log (by positivity : (0 : ℝ) < ((k + 2 : ℕ) : ℝ))
              (by exact_mod_cast hkH)) hε)
      _ = ((n - 1 : ℕ) : ℝ) * (ε * Real.log H) := by simp
      _ ≤ (n : ℝ) * (ε * Real.log H) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n 1) hB

/-- Literal charge-corrected finite residual on every included positive site. -/
theorem q_residual_head_identity (ε : ℝ) (N n : ℕ)
    (hn : 0 < n) (hnN : n ≤ N) :
    qSequence (qOne - qDampedMobiusPartial ε N) n =
      (n : ℝ) * realCharge ε N - (dampedMobiusPrefix ε n - 1) := by
  have he := congrFun (qSequenceLinear.map_sub qOne (qDampedMobiusPartial ε N)) n
  change qSequence (_ - _) n = qSequence qOne n - qSequence (qDampedMobiusPartial ε N) n at he
  rw [he, qSequence_qOne]
  simp only [qOneSequence, if_neg (ne_of_gt hn)]
  rw [qDampedMobiusPartial, toQ_sequence,
    arithmeticFloorHilbertPartial_sequence_of_le (dampedMobiusWeight ε) N n hnN]
  change 1 - (dampedMobiusPrefix ε n - (n : ℝ) * realCharge ε N) = _
  ring

/-- Endpoint envelope of the exact interval containing the normalized head
residual. This retains the sign of the finite reciprocal charge. -/
def headEnvelope (ε : ℝ) (N H : ℕ) : ℝ :=
  max |realCharge ε N| |realCharge ε N - ε * Real.log H|

theorem headEnvelope_nonneg (ε : ℝ) (N H : ℕ) :
    0 ≤ headEnvelope ε N H :=
  (abs_nonneg _).trans (le_max_left _ _)

/-- The signed endpoint envelope is no larger than the triangle envelope. -/
theorem headEnvelope_le_triangle {ε : ℝ} (hε : 0 ≤ ε)
    (N H : ℕ) (hH : 1 ≤ H) :
    headEnvelope ε N H ≤ |realCharge ε N| + ε * Real.log H := by
  have hL : 0 ≤ ε * Real.log H :=
    mul_nonneg hε (Real.log_nonneg (by exact_mod_cast hH))
  apply max_le
  · linarith
  · simpa only [abs_of_nonneg hL] using
      abs_sub (realCharge ε N) (ε * Real.log H)

/-- The normalized residual lies between A-ε log H and A, so its absolute
value is bounded by the larger endpoint magnitude, retaining the sign of A. -/
theorem q_residual_head_abs_le_envelope {ε : ℝ} (hε : 0 ≤ ε)
    (N H n : ℕ) (hn : 0 < n) (hnH : n ≤ H) (hHN : H ≤ N) :
    |qSequence (qOne - qDampedMobiusPartial ε N) n| ≤
      (n : ℝ) * headEnvelope ε N H := by
  have hb := dampedPrefix_sub_one_bounds hε hn hnH
  have hupper : realCharge ε N ≤ headEnvelope ε N H :=
    (le_abs_self _).trans (le_max_left _ _)
  have hlower : -headEnvelope ε N H ≤ realCharge ε N - ε * Real.log H :=
    (neg_le_neg (le_max_right _ _)).trans (neg_abs_le _)
  have hu := mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hl := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [q_residual_head_identity ε N n hn (hnH.trans hHN)]
  apply abs_le.mpr
  constructor
  · nlinarith only [hl, hb.2]
  · nlinarith only [hu, hb.1]

/-- The simpler triangle envelope follows from the stronger signed bound. -/
theorem q_residual_head_abs_le {ε : ℝ} (hε : 0 ≤ ε)
    (N H n : ℕ) (hn : 0 < n) (hnH : n ≤ H) (hHN : H ≤ N) :
    |qSequence (qOne - qDampedMobiusPartial ε N) n| ≤
      (n : ℝ) * (|realCharge ε N| + ε * Real.log H) := by
  exact (q_residual_head_abs_le_envelope hε N H n hn hnH hHN).trans
    (mul_le_mul_of_nonneg_left (headEnvelope_le_triangle hε N H (by omega))
      (Nat.cast_nonneg n))

end RiemannResearch.RH.Pareto.BalazardDeRoton

namespace RiemannResearch.RH.Pareto.BalazardDeRoton
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric
open DampedMobiusSquarefreeClosure

/-- Exact full-energy discrepancy, with every physical summand retained. -/
theorem q_residual_metric_discrepancy (ε : ℝ) (N : ℕ) :
    zetaTwo * ‖qOne - qDampedMobiusPartial ε N‖ ^ 2 -
      ‖toPareto (qOne - qDampedMobiusPartial ε N)‖ ^ 2 =
      ∑' n : ℕ, (qSequence (qOne - qDampedMobiusPartial ε N) (n + 1)) ^ 2 /
        (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) := by
  rw [norm_identity, add_sub_cancel_left, metricCorrection_eq_physical]

/-- Unconditional signed-envelope estimate, retaining the exact Pareto tail. -/
theorem q_residual_discrepancy_le_signed_head_tail {ε : ℝ} (hε : 0 ≤ ε)
    (N H : ℕ) (hHN : H ≤ N) :
    metricCorrection (qOne - qDampedMobiusPartial ε N) ≤
      headEnvelope ε N H ^ 2 * Real.log ((H : ℝ) + 1) +
      (‖toPareto (qOne - qDampedMobiusPartial ε N)‖ ^ 2 -
        ∑ n ∈ Finset.range H, (toPareto (qOne - qDampedMobiusPartial ε N) n) ^ 2) /
        ((H : ℝ) + 1) :=
  metricCorrection_le_linear_head_log_tail _ H (headEnvelope_nonneg ε N H)
    (fun n hn hnH => q_residual_head_abs_le_envelope hε N H n hn hnH hHN)

/-- The memo's finite comparison, now for the actual squarefree legal vectors. -/
theorem q_residual_discrepancy_le_charge_log {ε : ℝ} (hε : 0 ≤ ε)
    (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N) :
    0 ≤ zetaTwo * ‖qOne - qDampedMobiusPartial ε N‖ ^ 2 -
        ‖toPareto (qOne - qDampedMobiusPartial ε N)‖ ^ 2 ∧
    zetaTwo * ‖qOne - qDampedMobiusPartial ε N‖ ^ 2 -
        ‖toPareto (qOne - qDampedMobiusPartial ε N)‖ ^ 2 ≤
      (|realCharge ε N| + ε * Real.log H) ^ 2 * Real.log ((H : ℝ) + 1) +
        ‖toPareto (qOne - qDampedMobiusPartial ε N)‖ ^ 2 / ((H : ℝ) + 1) := by
  rw [norm_identity, add_sub_cancel_left]
  refine ⟨metricCorrection_nonneg _, ?_⟩
  apply metricCorrection_le_linear_head_log
  · exact add_nonneg (abs_nonneg _) (mul_nonneg hε
      (Real.log_nonneg (by exact_mod_cast hH)))
  · intro n hn hnH
    exact q_residual_head_abs_le hε N H n hn hnH hHN

/-- Conditional sharp P/Q transfer: the relative head budget remains explicit. -/
theorem q_residual_norm_ratio_tendsto_one
    (ε : ℕ → ℝ) (N H : ℕ → ℕ)
    (hε : ∀ j, 0 ≤ ε j) (hHN : ∀ j, H j ≤ N j)
    (hpos : ∀ j, 0 < ‖toPareto (qOne - qDampedMobiusPartial (ε j) (N j))‖ ^ 2)
    (hH : Filter.Tendsto H Filter.atTop Filter.atTop)
    (hbudget : Filter.Tendsto (fun j => headEnvelope (ε j) (N j) (H j) ^ 2 *
      Real.log ((H j : ℝ) + 1) /
        ‖toPareto (qOne - qDampedMobiusPartial (ε j) (N j))‖ ^ 2)
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun j =>
      zetaTwo * ‖qOne - qDampedMobiusPartial (ε j) (N j)‖ ^ 2 /
        ‖toPareto (qOne - qDampedMobiusPartial (ε j) (N j))‖ ^ 2)
      Filter.atTop (𝓝 1) :=
  norm_ratio_tendsto_one_of_linear_heads _ H _
    (fun j => headEnvelope_nonneg (ε j) (N j) (H j))
    (fun j n hn hnH => q_residual_head_abs_le_envelope (hε j) _ _ n hn hnH (hHN j))
    hpos hH hbudget

end RiemannResearch.RH.Pareto.BalazardDeRoton
