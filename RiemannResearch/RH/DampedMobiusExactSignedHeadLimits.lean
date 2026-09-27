/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.DampedMobiusSignedHeadClosure
import RiemannResearch.RH.DampedMobiusHalfEndpoint

/-!
# The actual diagonal and exact ordered signed-head limits

This module uses the actual damped Mobius residue atoms, their previously
proved summable squared norms, and the finite signed Gram identity.
Dominated convergence for the nonnegative diagonal produces the exact
iterated signed limit whenever actual centered finite energy is known.
The residue cutoff tends to infinity before the physical head.
Absolute convergence of the signed off-diagonal is not asserted.

Source for the unconditional energy application: J.-F. Burnol,
"On an analytic estimate in the theory of the Riemann zeta function and a
theorem of Baez-Duarte", Section 4, Lemma 4.1,
https://arxiv.org/abs/math/0202166, already realized by the imported
endpoint and strict-range providers. The limit arguments here are
elementary consequences of the verified infrastructure; no novelty
claim is made. Small-damping finite energy remains an open premise.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- The actual arithmetic diagonal, rather than its p-series majorant. -/
def dampedMobiusExactDiagonal (ε : ℝ) : ℝ :=
  ∑' m : ℕ, ‖arithmeticResidueTerm (dampedMobiusWeight ε) m‖ ^ 2

theorem dampedMobiusExactDiagonal_nonneg (ε : ℝ) :
    0 ≤ dampedMobiusExactDiagonal ε :=
  tsum_nonneg (fun _ => sq_nonneg _)

theorem dampedMobiusExactDiagonal_le_budget {ε : ℝ} (hε : 0 < ε) :
    dampedMobiusExactDiagonal ε ≤ dampedMobiusDiagonalBudget ε := by
  have h := Summable.tsum_le_tsum
    (dampedMobiusResidue_norm_sq_le ε)
    (dampedMobiusResidue_norm_sq_summable hε)
    ((dampedMobiusDiagonalMajorant_summable hε).mul_left 2)
  simpa only [dampedMobiusExactDiagonal, dampedMobiusDiagonalBudget,
    tsum_mul_left] using h

theorem dampedMobiusHeadDiagonal_le_exact {ε : ℝ} (hε : 0 < ε) (H M : ℕ) :
    dampedMobiusHeadDiagonal ε H M ≤ dampedMobiusExactDiagonal ε := by
  exact (Finset.sum_le_sum (fun m _ =>
    paretoHeadPairing_self_le H (arithmeticResidueTerm (dampedMobiusWeight ε) m))).trans
    (Summable.sum_le_tsum (Finset.range M) (fun _ _ => sq_nonneg _)
      (dampedMobiusResidue_norm_sq_summable hε))

/-- Complete diagonal on a finite physical head; the residue index is summed first. -/
def dampedMobiusCompletedHeadDiagonal (ε : ℝ) (H : ℕ) : ℝ :=
  ∑' m : ℕ, paretoHeadPairing H
    (arithmeticResidueTerm (dampedMobiusWeight ε) m)
    (arithmeticResidueTerm (dampedMobiusWeight ε) m)

theorem dampedMobius_headDiagonal_summable {ε : ℝ} (hε : 0 < ε) (H : ℕ) :
    Summable (fun m : ℕ => paretoHeadPairing H
      (arithmeticResidueTerm (dampedMobiusWeight ε) m)
      (arithmeticResidueTerm (dampedMobiusWeight ε) m)) :=
  Summable.of_nonneg_of_le
    (fun _ => paretoHeadPairing_self_nonneg H _)
    (fun _ => paretoHeadPairing_self_le H _)
    (dampedMobiusResidue_norm_sq_summable hε)

theorem dampedMobius_headDiagonal_tendsto {ε : ℝ} (hε : 0 < ε) (H : ℕ) :
    Tendsto (dampedMobiusHeadDiagonal ε H) atTop
      (𝓝 (dampedMobiusCompletedHeadDiagonal ε H)) :=
  (dampedMobius_headDiagonal_summable hε H).hasSum.tendsto_sum_nat

theorem dampedMobiusCompletedHeadDiagonal_le_exact {ε : ℝ} (hε : 0 < ε) (H : ℕ) :
    dampedMobiusCompletedHeadDiagonal ε H ≤ dampedMobiusExactDiagonal ε :=
  Summable.tsum_le_tsum (fun _ => paretoHeadPairing_self_le H _)
    (dampedMobius_headDiagonal_summable hε H)
    (dampedMobiusResidue_norm_sq_summable hε)

private theorem paretoHeadPairing_self_tendsto (f : ThresholdHilbert) :
    Tendsto (fun H => paretoHeadPairing H f f) atTop (𝓝 (‖f‖ ^ 2)) := by
  rw [hilbert_norm_weighted_sq]
  simpa only [paretoHeadPairing, mul_assoc, ← pow_two] using
    (hilbertSequence_square_summable f).hasSum.tendsto_sum_nat

/-- The full diagonal limit is unconditional for every epsilon > 0. -/
theorem dampedMobius_completedHeadDiagonal_tendsto {ε : ℝ} (hε : 0 < ε) :
    Tendsto (dampedMobiusCompletedHeadDiagonal ε) atTop
      (𝓝 (dampedMobiusExactDiagonal ε)) := by
  apply tendsto_tsum_of_dominated_convergence
    (dampedMobiusResidue_norm_sq_summable hε)
    (fun m => paretoHeadPairing_self_tendsto
      (arithmeticResidueTerm (dampedMobiusWeight ε) m))
  exact Eventually.of_forall (fun H m => by
    rw [Real.norm_eq_abs, abs_of_nonneg (paretoHeadPairing_self_nonneg H _)]
    exact paretoHeadPairing_self_le H _)

/-- The signed residue-cutoff limit on one finite physical head. -/
def dampedMobiusSignedHeadLimit (ε : ℝ) (H : ℕ) : ℝ :=
  (∑ n ∈ Finset.range H, positiveWeight n *
    (dampedMobiusPrefix ε n - (n : ℝ) *
      (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) -
    dampedMobiusCompletedHeadDiagonal ε H

/-- All signed off-diagonal terms are retained. The residue cutoff tends to
infinity at a fixed head; no absolute off-diagonal summability is asserted. -/
theorem dampedMobius_offDiagonal_fixed_head_tendsto {ε : ℝ} (hε : 0 < ε) (H : ℕ) :
    Tendsto (dampedMobiusHeadOffDiagonal ε H) atTop
      (𝓝 (dampedMobiusSignedHeadLimit ε H)) := by
  have ht := (dampedMobius_partial_head_tendsto hε H).sub
    (dampedMobius_headDiagonal_tendsto hε H)
  convert ht using 1
  · funext M
    rw [dampedMobius_partial_head_eq_signed]
    ring
  · rfl

/-- Exact iterated signed limit under the explicit actual-energy premise.
First the residue cutoff tends to infinity, then the physical head does. -/
theorem dampedMobius_signedHeadLimit_tendsto_of_summable
    {ε : ℝ} (hε : 0 < ε)
    (henergy : Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) *
        (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2)) :
    Tendsto (dampedMobiusSignedHeadLimit ε) atTop
      (𝓝 ((∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix ε n - (n : ℝ) *
          (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) -
          dampedMobiusExactDiagonal ε)) :=
  henergy.hasSum.tendsto_sum_nat.sub (dampedMobius_completedHeadDiagonal_tendsto hε)

/-- The exact iterated-limit formula throughout the proved unconditional range. -/
theorem dampedMobius_signedHeadLimit_tendsto_of_half_le
    {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) :
    Tendsto (dampedMobiusSignedHeadLimit ε) atTop
      (𝓝 ((∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix ε n - (n : ℝ) *
          (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) -
          dampedMobiusExactDiagonal ε)) :=
  dampedMobius_signedHeadLimit_tendsto_of_summable
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hε)
    (centered_dampedMobius_square_summable_of_half_le hε)

end RiemannResearch.RH.Pareto
