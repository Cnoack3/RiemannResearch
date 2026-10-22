/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ParetoWeights
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact metric correction with approximate physical heads

Source: the finite P/Q comparison in
`BalazardDeRotonResearch20261019.md`, developed from the user-requested RH
continuation of 19 October 2026. The identities follow directly from the
literal P and Q probability weights. This module proves the reusable
Hilbert-space estimates; it does not assume a particular arithmetic family.

The exact head/tail decomposition is primary. The upper estimate retains
the actual Pareto tail before the simpler full-energy bound is used.
Leading-constant-one transfer is conditional on a relative head budget,
and does not imply that the full approximation error tends to zero.
-/
noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QParetoMetric
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer

/-- Exact decomposition, including the entire infinite correction tail. -/
theorem metricCorrection_head_tail (f : QHilbert) (H : ℕ) :
    metricCorrection f =
      (∑ n ∈ Finset.range H, (toPareto f n) ^ 2 / ((n : ℝ) + 1)) +
      ∑' n : ℕ, (toPareto f (n + H)) ^ 2 / ((n + H : ℕ) + 1 : ℝ) := by
  rw [metricCorrection_eq_tsum]
  exact ((reciprocal_energy_summable (toPareto f)).sum_add_tsum_nat_add H).symm

/-- The reciprocal multiplier is bounded by its first tail value. -/
theorem metricCorrection_le_head_tail (f : QHilbert) (H : ℕ) :
    metricCorrection f ≤
      (∑ n ∈ Finset.range H, (toPareto f n) ^ 2 / ((n : ℝ) + 1)) +
      (‖toPareto f‖ ^ 2 - ∑ n ∈ Finset.range H, (toPareto f n) ^ 2) /
        ((H : ℝ) + 1) := by
  have hs := hilbert_coordinate_square_summable (toPareto f)
  have hc := reciprocal_energy_summable (toPareto f)
  have he := hs.sum_add_tsum_nat_add H
  rw [← hilbert_norm_sq] at he
  have ht : (∑' n : ℕ, (toPareto f (n + H)) ^ 2) =
      ‖toPareto f‖ ^ 2 - ∑ n ∈ Finset.range H, (toPareto f n) ^ 2 := by
    linarith
  rw [metricCorrection_head_tail f H, ← ht, ← tsum_div_const]
  apply add_le_add le_rfl
  apply Summable.tsum_le_tsum _ (hc.comp_injective (add_left_injective H))
    ((hs.comp_injective (add_left_injective H)).div_const _)
  intro n
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem metricCorrection_le_head_full_tail (f : QHilbert) (H : ℕ) :
    metricCorrection f ≤
      (∑ n ∈ Finset.range H, (toPareto f n) ^ 2 / ((n : ℝ) + 1)) +
      ‖toPareto f‖ ^ 2 / ((H : ℝ) + 1) := by
  apply (metricCorrection_le_head_tail f H).trans
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact sub_le_self _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem metricCorrection_head_le_of_linear_bound (f : QHilbert) (H : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hhead : ∀ k, 0 < k → k ≤ H → |qSequence f k| ≤ (k : ℝ) * B) :
    (∑ n ∈ Finset.range H, (toPareto f n) ^ 2 / ((n : ℝ) + 1)) ≤
      B ^ 2 * ∑ n ∈ Finset.range H, 1 / ((n : ℝ) + 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hnH : n + 1 ≤ H := by have := Finset.mem_range.mp hn; omega
  have hsq : (qSequence f (n + 1)) ^ 2 ≤ (((n : ℝ) + 1) * B) ^ 2 := by
    simpa only [sq_abs, Nat.cast_add, Nat.cast_one] using
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg (n + 1)) hB)).mpr
        (hhead (n + 1) (by omega) hnH)
  rw [← hilbertSequence_weighted_square (toPareto f) n, toPareto_sequence,
    positiveWeight_succ]
  unfold paretoWeight
  calc
    _ ≤ (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) *
        (((n : ℝ) + 1) * B) ^ 2) / ((n : ℝ) + 1) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity)
    _ = _ := by
      have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp

theorem metricCorrection_le_linear_head_harmonic (f : QHilbert) (H : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hhead : ∀ k, 0 < k → k ≤ H → |qSequence f k| ≤ (k : ℝ) * B) :
    metricCorrection f ≤
      B ^ 2 * (∑ n ∈ Finset.range H, 1 / ((n : ℝ) + 2)) +
        ‖toPareto f‖ ^ 2 / ((H : ℝ) + 1) :=
  (metricCorrection_le_head_full_tail f H).trans
    (add_le_add (metricCorrection_head_le_of_linear_bound f H hB hhead) le_rfl)

private theorem shifted_harmonic_le_log (H : ℕ) :
    (∑ n ∈ Finset.range H, 1 / ((n : ℝ) + 2)) ≤ Real.log ((H : ℝ) + 1) := by
  have h := harmonic_le_one_add_log (H + 1)
  have hcast (n : ℕ) : (harmonic n : ℝ) =
      ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) := by
    simp [harmonic, one_div]
  rw [hcast, Finset.sum_range_succ'] at h
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, one_div_one] at h
  have he : (∑ k ∈ Finset.range H, 1 / ((k : ℝ) + 1 + 1)) =
      ∑ k ∈ Finset.range H, 1 / ((k : ℝ) + 2) := by
    congr 1
    ext k
    congr 1
    ring
  rw [he] at h
  linarith

theorem metricCorrection_le_linear_head_log (f : QHilbert) (H : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hhead : ∀ k, 0 < k → k ≤ H → |qSequence f k| ≤ (k : ℝ) * B) :
    metricCorrection f ≤ B ^ 2 * Real.log ((H : ℝ) + 1) +
      ‖toPareto f‖ ^ 2 / ((H : ℝ) + 1) :=
  (metricCorrection_le_linear_head_harmonic f H hB hhead).trans
    (add_le_add (mul_le_mul_of_nonneg_left (shifted_harmonic_le_log H)
      (sq_nonneg B)) le_rfl)

/-- Approximate heads with the actual Pareto tail energy retained. -/
theorem metricCorrection_le_linear_head_log_tail (f : QHilbert) (H : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hhead : ∀ k, 0 < k → k ≤ H → |qSequence f k| ≤ (k : ℝ) * B) :
    metricCorrection f ≤ B ^ 2 * Real.log ((H : ℝ) + 1) +
      (‖toPareto f‖ ^ 2 - ∑ n ∈ Finset.range H, (toPareto f n) ^ 2) /
        ((H : ℝ) + 1) := by
  apply (metricCorrection_le_head_tail f H).trans
  apply add_le_add _ le_rfl
  exact (metricCorrection_head_le_of_linear_bound f H hB hhead).trans
    (mul_le_mul_of_nonneg_left (shifted_harmonic_le_log H) (sq_nonneg B))

/-- A vanishing relative head budget gives leading-constant-one transfer.
The Pareto error is not assumed to tend to zero. -/
theorem norm_ratio_tendsto_one_of_linear_heads
    (f : ℕ → QHilbert) (H : ℕ → ℕ) (B : ℕ → ℝ)
    (hB : ∀ j, 0 ≤ B j)
    (hhead : ∀ j k, 0 < k → k ≤ H j →
      |qSequence (f j) k| ≤ (k : ℝ) * B j)
    (hpos : ∀ j, 0 < ‖toPareto (f j)‖ ^ 2)
    (hH : Tendsto H atTop atTop)
    (hbudget : Tendsto (fun j => B j ^ 2 * Real.log ((H j : ℝ) + 1) /
      ‖toPareto (f j)‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun j => ZetaTwoProbability.zetaTwo * ‖f j‖ ^ 2 /
      ‖toPareto (f j)‖ ^ 2) atTop (𝓝 1) := by
  have hinv : Tendsto (fun j => 1 / ((H j : ℝ) + 1)) atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have ht := tendsto_inv_atTop_zero.comp
        ((tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp (tendsto_add_atTop_nat 1))
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, one_div] using ht
    exact hnat.comp hH
  have hd : Tendsto (fun j => metricCorrection (f j) / ‖toPareto (f j)‖ ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun j => div_nonneg (metricCorrection_nonneg _) (hpos j).le)
      (fun j => ?_) (by simpa only [add_zero] using hbudget.add hinv)
    have hh := div_le_div_of_nonneg_right
      (metricCorrection_le_linear_head_log (f j) (H j) (hB j) (hhead j)) (hpos j).le
    have he : (‖toPareto (f j)‖ ^ 2 / ((H j : ℝ) + 1)) /
        ‖toPareto (f j)‖ ^ 2 = 1 / ((H j : ℝ) + 1) := by
      rw [div_right_comm, div_self (ne_of_gt (hpos j))]
    simpa only [add_div, he] using hh
  have he (j : ℕ) : ZetaTwoProbability.zetaTwo * ‖f j‖ ^ 2 /
      ‖toPareto (f j)‖ ^ 2 = 1 + metricCorrection (f j) / ‖toPareto (f j)‖ ^ 2 := by
    rw [norm_identity, add_div, div_self (ne_of_gt (hpos j))]
  simp_rw [he]
  simpa only [add_zero] using hd.const_add 1

end RiemannResearch.RH.QParetoMetric
