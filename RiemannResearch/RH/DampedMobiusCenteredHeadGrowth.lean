/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.TwoScaleEnergyTransfer
import RiemannResearch.Analysis.FiniteWeightedEnergyComparison
import RiemannResearch.RH.DampedMobiusHeadApproximation
import RiemannResearch.RH.DampedMobiusSubhalfNormalization

/-!
# Actual centered finite-head growth below half damping

The normalized finite-conductor Hilbert energy theorem is transferred to the
actual centered arithmetic sequence on finite physical heads. The exact
completed diagonal and signed-head limits obey the same normalization.

Source: the two-scale argument developed in this session, using the checked
head-error, finite-energy comparison, and subhalf normalization providers.
These growing-denominator limits do not assert finite unnormalized energy.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto

/-- Energy of the actual centered arithmetic sequence on a finite physical head. -/
def dampedMobiusCenteredHeadEnergy (ε : ℝ) (H : ℕ) : ℝ :=
  ∑ n ∈ Finset.range H, positiveWeight n *
    (dampedMobiusPrefix ε n - (n : ℝ) *
      (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2

theorem dampedMobiusCenteredHeadEnergy_nonneg (ε : ℝ) (H : ℕ) :
    0 ≤ dampedMobiusCenteredHeadEnergy ε H :=
  Finset.sum_nonneg (fun n _ =>
    mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))

/-- Comparison with a finite conductor approximation, after signed-tail collapse. -/
theorem dampedMobius_centered_head_energy_le {ε : ℝ} (hε : 0 < ε)
    (H M : ℕ) (hHM : H ≤ M) (hM : 1 ≤ M) :
    dampedMobiusCenteredHeadEnergy ε H ≤
      2 * ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ^ 2 +
      (2 / ε ^ 2) * (H : ℝ) * (M : ℝ) ^ (-(2 * ε)) := by
  have hc := (RiemannResearch.Analysis.sum_weighted_sq_comparison_of_sub_sq_le
    (Finset.range H) positiveWeight
    (hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M))
    (fun n => dampedMobiusPrefix ε n -
      (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)
    (fun n _ => positiveWeight_nonneg n) _
    (dampedMobius_head_error_le hε H M hHM hM)).2
  have hn : (∑ n ∈ Finset.range H, positiveWeight n *
      (hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M) n)^2)
      ≤ ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖^2 := by
    simpa only [paretoHeadPairing, mul_assoc, ← pow_two] using
      paretoHeadPairing_self_le H
        (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M)
  change dampedMobiusCenteredHeadEnergy ε H ≤ _ at hc
  have he : 2 * ((H : ℝ) * (M : ℝ)^(-2*ε) / ε^2) =
      (2 / ε^2) * (H : ℝ) * (M : ℝ)^(-(2*ε)) := by
    rw [show -2 * ε = -(2 * ε) by ring]
    ring
  rw [he] at hc
  linarith

/-- Unconditional little-o growth of the actual centered finite-head energy
at every fixed positive damping below one half. -/
theorem dampedMobius_centered_head_energy_normalized_tendsto
    {ε : ℝ} (hε : 0 < ε) (hhalf : ε < 1 / 2) :
    Tendsto (fun H : ℕ => dampedMobiusCenteredHeadEnergy ε H /
      ((H + 1 : ℕ) : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  apply RiemannResearch.Analysis.two_scale_energy_tendsto_zero
    (dampedMobiusCenteredHeadEnergy ε)
    (fun M => 2 * ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖^2)
    (C := 2 / ε^2) (q := 2 * ε) (by positivity) (by positivity)
    (dampedMobiusCenteredHeadEnergy_nonneg ε)
  · simpa only [mul_div_assoc, mul_zero] using
      (dampedMobius_subhalf_normalized_energy_tendsto hhalf).const_mul 2
  · exact dampedMobius_centered_head_energy_le hε

/-- The completed nonnegative diagonal is negligible under the same normalization. -/
theorem dampedMobius_completed_head_diagonal_normalized_tendsto
    {ε : ℝ} (hε : 0 < ε) (hhalf : ε < 1 / 2) :
    Tendsto (fun H : ℕ => dampedMobiusCompletedHeadDiagonal ε H /
      ((H + 1 : ℕ) : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  have hp : 0 < 1 - 2 * ε := by linarith
  have hcast : Tendsto (fun H : ℕ => ((H + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi := (tendsto_rpow_neg_atTop hp).comp hcast
  have ht := (dampedMobius_completedHeadDiagonal_tendsto hε).mul hi
  have he (H : ℕ) : ((H + 1 : ℕ) : ℝ) ^ (-(1 - 2 * ε)) =
      (((H + 1 : ℕ) : ℝ) ^ (1 - 2 * ε))⁻¹ :=
    Real.rpow_neg (by positivity) _
  simpa only [Function.comp_def, he, div_eq_mul_inv, mul_zero] using ht

/-- The full signed conductor limit on each head has vanishing normalized growth.
The absolute value is taken only after the complete signed sum. -/
theorem dampedMobius_signed_head_limit_normalized_tendsto
    {ε : ℝ} (hε : 0 < ε) (hhalf : ε < 1 / 2) :
    Tendsto (fun H : ℕ => |dampedMobiusSignedHeadLimit ε H| /
      ((H + 1 : ℕ) : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  have ht := (dampedMobius_centered_head_energy_normalized_tendsto hε hhalf).sub
    (dampedMobius_completed_head_diagonal_normalized_tendsto hε hhalf)
  simp only [sub_zero] at ht
  have ha := ht.abs
  have he (H : ℕ) : |((H + 1 : ℕ) : ℝ) ^ (1 - 2 * ε)| =
      ((H + 1 : ℕ) : ℝ) ^ (1 - 2 * ε) :=
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)
  simpa only [← sub_div, dampedMobiusSignedHeadLimit, dampedMobiusCenteredHeadEnergy,
    abs_div, he, abs_zero] using ha

end RiemannResearch.RH.Pareto
