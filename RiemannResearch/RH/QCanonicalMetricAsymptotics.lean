/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QCanonicalMovingCovariance
import RiemannResearch.RH.CanonicalMobiusMovingCutoff
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Unconditional metric asymptotics and sharper canonical covariance in Q

Source: the user's Pareto-to-Q transfer request, 15 October 2026.
The exact head and checked stretched-PNT normalized-energy estimate are the
existing arithmetic providers. The new metric correction is dominated by
that normalized energy, hence tends to zero even without a uniform bound
on the unnormalized residual energies.

This is an absolute discrepancy limit for scaled energies, not a proof
that either complete canonical approximation error tends to zero.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QCanonicalMetricAsymptotics
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric
open QCanonicalMovingCovariance

theorem residual_head_zero (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    qSequence (residual N) k = 0 := by
  rw [residual_sequence]
  change qOneSequence k - canonicalMobiusHead N k = 0
  rw [canonicalMobiusHead_exact N k hk hkN]
  simp [qOneSequence, Nat.ne_of_gt hk]

theorem pareto_energyRate_tendsto_zero :
    Tendsto Pareto.MovingCovariance.energyRate atTop (𝓝 0) := by
  apply squeeze_zero (fun N => Pareto.MovingCovariance.energyRate_nonneg N)
    (fun N => ?_) Pareto.MovingCovariance.explicitCutoff_pair_budget_tendsto
  have hK : 0 ≤ (Pareto.MovingCovariance.explicitCutoff N : ℝ) := Nat.cast_nonneg _
  have hs : 1 ≤ (1 + 2 * (Pareto.MovingCovariance.explicitCutoff N : ℝ)) ^ 2 := by
    nlinarith
  nlinarith [mul_nonneg (Pareto.MovingCovariance.energyRate_nonneg N) (sub_nonneg.mpr hs)]

/-- Exact identity for the actual canonical residuals in the two measures. -/
theorem canonical_energy_identity (N : ℕ) :
    zetaTwo * ‖residual N‖ ^ 2 =
      ‖Pareto.MovingCovariance.residual N‖ ^ 2 + metricCorrection (residual N) := by
  simpa only [toPareto_residual] using norm_identity (residual N)

theorem correction_le_energyRate (N : ℕ) :
    metricCorrection (residual N) ≤ Pareto.MovingCovariance.energyRate N := by
  simpa only [toPareto_residual, Pareto.MovingCovariance.energyRate] using
    metricCorrection_le_of_head_zero (residual N) N (residual_head_zero N)

/-- Unconditional: the positive metric correction tends to zero. -/
theorem correction_tendsto_zero :
    Tendsto (fun N => metricCorrection (residual N)) atTop (𝓝 0) :=
  squeeze_zero (fun _ => metricCorrection_nonneg _) correction_le_energyRate
    pareto_energyRate_tendsto_zero

/-- Unconditional equality of the complete scaled energies up to a vanishing
absolute discrepancy. No bounded canonical-energy hypothesis is used. -/
theorem energy_discrepancy_tendsto_zero :
    Tendsto (fun N => zetaTwo * ‖residual N‖ ^ 2 -
      ‖Pareto.MovingCovariance.residual N‖ ^ 2) atTop (𝓝 0) := by
  have he (N : ℕ) : zetaTwo * ‖residual N‖ ^ 2 -
      ‖Pareto.MovingCovariance.residual N‖ ^ 2 = metricCorrection (residual N) := by
    rw [canonical_energy_identity]
    ring
  simpa only [he] using correction_tendsto_zero

/-- The existing explicit logarithmic rate also bounds the new discrepancy.
The constant and onset are existential, exactly as in the checked PNT provider. -/
theorem correction_eventual_log_square :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ N in atTop,
      metricCorrection (residual N) ≤ D / Pareto.MovingCovariance.logScale N ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := Pareto.MovingCovariance.energyRate_eventual_log_square
  refine ⟨D, hD, ?_⟩
  filter_upwards [hbound] with N hN
  exact (correction_le_energyRate N).trans hN

/-- Head-dependent comparison replaces the old global factor two. -/
theorem energyRate_le_pareto_sharp (N : ℕ) :
    energyRate N ≤ ((1 + 1 / ((N : ℝ) + 1)) / zetaTwo) *
      Pareto.MovingCovariance.energyRate N := by
  have h := norm_sq_le_of_head_zero (residual N) N (residual_head_zero N)
  rw [toPareto_residual] at h
  have hn : ‖residual N‖ ^ 2 ≤ ((1 + 1 / ((N : ℝ) + 1)) / zetaTwo) *
      ‖Pareto.MovingCovariance.residual N‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ zetaTwo_pos).mpr
    simpa only [mul_comm] using h
  exact (div_le_div_of_nonneg_right hn (by positivity)).trans_eq (by
    unfold Pareto.MovingCovariance.energyRate
    ring)

/-- Sharper complete covariance estimate against any bounded physical test. -/
theorem inner_sq_le_sharp (f : QHilbert) (N : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ n, 0 < n → |qSequence f n| ≤ A) :
    (inner ℝ f (residual N)) ^ 2 ≤
      ((1 + 1 / ((N : ℝ) + 1)) / zetaTwo) * A ^ 2 * energyRate N := by
  have he : ∀ n < N, residual N n = 0 := by
    intro n hn
    have hs := residual_head_zero N (n + 1) (by omega) (by omega)
    rw [qSequence_succ] at hs
    exact (div_eq_zero_iff.mp hs).resolve_right
      (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n)))
  exact (hilbertTailShift_inner_sq_le f _ N he).trans
    ((mul_le_mul_of_nonneg_right
      (QParetoMetric.tail_norm_sq_le_of_bounded f N A hA hf)
      (sq_nonneg _)).trans_eq (by unfold energyRate; ring))

/-- The old (2/ζ(2))² constant becomes ((1+1/(N+1))/ζ(2))². -/
theorem covariance_sq_le_sharp (K N : ℕ) (hK : 0 < K) :
    (inner ℝ (residual K) (residual N)) ^ 2 ≤
      ((1 + 1 / ((N : ℝ) + 1)) / zetaTwo) ^ 2 * (1 + 2 * (K : ℝ)) ^ 2 *
        Pareto.MovingCovariance.energyRate N := by
  calc
    _ ≤ ((1 + 1 / ((N : ℝ) + 1)) / zetaTwo) *
        (1 + 2 * (K : ℝ)) ^ 2 * energyRate N :=
      inner_sq_le_sharp _ N _ (by positivity) (physical_bound K hK)
    _ ≤ ((1 + 1 / ((N : ℝ) + 1)) / zetaTwo) *
        (1 + 2 * (K : ℝ)) ^ 2 *
        (((1 + 1 / ((N : ℝ) + 1)) / zetaTwo) *
          Pareto.MovingCovariance.energyRate N) :=
      mul_le_mul_of_nonneg_left (energyRate_le_pareto_sharp N) (by positivity [zetaTwo_pos])
    _ = _ := by ring

end RiemannResearch.RH.QCanonicalMetricAsymptotics
