/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DampedMobiusSquarefreeClosure
import RiemannResearch.RH.DampedMobiusHeadApproximation
import RiemannResearch.RH.QConductorEstimates
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.DampedMobiusReciprocalHilbert

/-!
# Actual smoothed Mobius series and complete finite-cutoff errors

Source: Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf, formula (14)
and Theorem 6.2. Reciprocal smoothing supplies an inverse-conductor atom
bound, hence absolute Hilbert-series convergence for every positive damping.
Coordinate continuity identifies this genuine series with the centered
arithmetic formula. The integral-test tail gives a full Q truncation budget.

All finite cutoffs belong to the squarefree legal span. No unsmoothed
infinite-series membership or uniform unsmoothed-energy bound is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.DampedMobiusSmoothedSeries
open Pareto ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal QParetoEquivalence
open DampedMobiusSquarefreeClosure SquarefreeRadicalDifference

def qDampedSmoothedTerm (ε : ℝ) (m : ℕ) : QHilbert :=
  dampedMobiusWeight ε (m + 1) • B (qResidue (m + 1))

/-- The reciprocal atom gains a full inverse conductor. -/
theorem qDampedSmoothedTerm_norm_le (ε : ℝ) (m : ℕ) :
    ‖qDampedSmoothedTerm ε m‖ ≤ ((m + 1 : ℕ) : ℝ) ^ (-ε - 1) := by
  have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [qDampedSmoothedTerm, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |dampedMobiusWeight ε (m + 1)| * (1 / ((m + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (B_qResidue_norm_le (m + 1) (by omega))
        (abs_nonneg _)
    _ = |dampedMobiusWeight ε (m + 1) / ((m + 1 : ℕ) : ℝ)| := by
      rw [abs_div, abs_of_pos hm]
      ring
    _ ≤ _ := dampedMobius_density_term_abs_le ε m

/-- Absolute convergence holds after reciprocal smoothing at every positive
damping, in contrast with the unsmoothed arithmetic Hilbert series. -/
theorem qDampedSmoothedTerm_norm_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (fun m : ℕ => ‖qDampedSmoothedTerm ε m‖) := by
  have hp : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (-ε - 1)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith only [hε]))
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (qDampedSmoothedTerm_norm_le ε) hp

theorem qDampedSmoothedTerm_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (qDampedSmoothedTerm ε) :=
  (qDampedSmoothedTerm_norm_summable hε).of_norm

def qDampedMobiusSmoothed (ε : ℝ) : QHilbert :=
  -(∑' m : ℕ, qDampedSmoothedTerm ε m)

/-- The unsmoothed finite cutoff is literally in the squarefree legal span. -/
theorem qDampedMobiusPartial_mem_squarefreeSpan (ε : ℝ) (N : ℕ) :
    qDampedMobiusPartial ε N ∈ qSquarefreeCRTSpan := by
  classical
  rw [qDampedMobiusPartial_eq]
  apply qSquarefreeCRTSpan.neg_mem
  apply qSquarefreeCRTSpan.sum_mem
  intro m _
  by_cases hsf : Squarefree (m + 1)
  · by_cases htwo : 2 ≤ m + 1
    · apply qSquarefreeCRTSpan.smul_mem
      exact Submodule.subset_span ⟨⟨m + 1, htwo, hsf⟩, rfl⟩
    · have he : m + 1 = 1 := by omega
      rw [he, qResidue_one, smul_zero]
      exact qSquarefreeCRTSpan.zero_mem
  · have hz : dampedMobiusWeight ε (m + 1) = 0 := by
      simp [dampedMobiusWeight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
    rw [hz, zero_smul]
    exact qSquarefreeCRTSpan.zero_mem

/-- Every partial smoothed sum is the reciprocal of the actual legal cutoff. -/
theorem qDampedMobiusPartial_B_eq (ε : ℝ) (N : ℕ) :
    B (qDampedMobiusPartial ε N) =
      -(∑ m ∈ Finset.range N, qDampedSmoothedTerm ε m) := by
  rw [qDampedMobiusPartial_eq, map_neg, map_sum]
  simp only [map_smul, qDampedSmoothedTerm]

theorem qDampedMobiusPartial_B_tendsto {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => B (qDampedMobiusPartial ε N)) atTop
      (𝓝 (qDampedMobiusSmoothed ε)) := by
  simpa only [qDampedMobiusPartial_B_eq, qDampedMobiusSmoothed] using
    (qDampedSmoothedTerm_summable hε).hasSum.tendsto_sum_nat.neg

/-- The norm difference retains every omitted signed conductor. -/
theorem qDampedMobiusSmoothed_partial_error_eq {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    qDampedMobiusSmoothed ε - B (qDampedMobiusPartial ε N) =
      -(∑' j : ℕ, qDampedSmoothedTerm ε (j + N)) := by
  rw [qDampedMobiusSmoothed, qDampedMobiusPartial_B_eq,
    ← (qDampedSmoothedTerm_summable hε).sum_add_tsum_nat_add N]
  abel

-- The shifted infinite-series comparison needs additional elaboration budget;
-- its scalar arithmetic uses only the positive-damping premise.
set_option maxHeartbeats 800000 in
-- Integral and shifted infinite-sum elaboration exceeds the default heartbeat budget.
/-- A complete-Q truncation estimate valid for all ε>0. -/
theorem qDampedMobiusSmoothed_partial_error_le {ε : ℝ} (hε : 0 < ε)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖qDampedMobiusSmoothed ε - B (qDampedMobiusPartial ε N)‖ ≤
      (N : ℝ) ^ (-ε) / ε := by
  have hs : Summable (fun j : ℕ => ‖qDampedSmoothedTerm ε (j + N)‖) :=
    (summable_nat_add_iff N).mpr (qDampedSmoothedTerm_norm_summable hε)
  have hp : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (-ε - 1)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith only [hε]))
  rw [qDampedMobiusSmoothed_partial_error_eq hε N, norm_neg]
  calc
    _ ≤ ∑' j : ℕ, ‖qDampedSmoothedTerm ε (j + N)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ) ^ (-ε - 1) :=
      hs.tsum_le_tsum (fun j => qDampedSmoothedTerm_norm_le ε (j + N))
        ((summable_nat_add_iff N).mpr hp)
    _ ≤ _ := by
      have h := Real.tsum_nat_rpow_tail_le (p := ε + 1) (by linarith only [hε]) hN
      simpa only [show -(ε + 1) = -ε - 1 by ring,
        show 1 - (ε + 1) = -ε by ring, show ε + 1 - 1 = ε by ring] using h

/-- Exact pointwise identification of the genuine smoothed Hilbert series.
The unsmoothed centered sequence is not assumed to be in QHilbert. -/
theorem qDampedMobiusSmoothed_sequence {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    qSequence (qDampedMobiusSmoothed ε) n =
      (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) / ((n : ℝ) + 1) := by
  have hleft := ((continuous_qSequence n).tendsto (qDampedMobiusSmoothed ε)).comp
    (qDampedMobiusPartial_B_tendsto hε)
  have hright : Tendsto (fun N => qSequence (B (qDampedMobiusPartial ε N)) n) atTop
      (𝓝 ((dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) / ((n : ℝ) + 1))) := by
    simpa only [qSequence_B, qDampedMobiusPartial, toQ_sequence] using
      (dampedMobius_partial_coordinate_tendsto hε n).div_const ((n : ℝ) + 1)
  exact tendsto_nhds_unique hleft hright

open DampedMobiusReciprocalHilbert

/-- The coordinate construction and the actual signed smoothed series coincide. -/
theorem qDampedMobiusSmoothed_eq_reciprocalQ {ε : ℝ} (hε : 0 < ε) :
    qDampedMobiusSmoothed ε = dampedMobiusReciprocalQ ε hε := by
  apply qSequence_injective
  funext n
  rw [qDampedMobiusSmoothed_sequence hε, qSequence_dampedMobiusReciprocalQ]
  rfl

/-- A concrete unconditional approximation theorem for the actual finite
squarefree legal damped Mobius combination, including its entire Q tail. -/
theorem qDampedMobiusPartial_reciprocal_error_le {ε : ℝ} (hε : 0 < ε)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖B (qDampedMobiusPartial ε N - qOne)‖ ≤
      ε * ‖qLogEnvelope‖ + (N : ℝ) ^ (-ε) / ε := by
  rw [map_sub]
  have ht : ‖B (qDampedMobiusPartial ε N) - qDampedMobiusSmoothed ε‖ ≤
      (N : ℝ) ^ (-ε) / ε := by
    rw [norm_sub_rev]
    exact qDampedMobiusSmoothed_partial_error_le hε hN
  have hc : ‖qDampedMobiusSmoothed ε - B qOne‖ ≤ ε * ‖qLogEnvelope‖ := by
    rw [qDampedMobiusSmoothed_eq_reciprocalQ hε]
    exact dampedMobiusReciprocalQ_error_norm_le hε
  calc
    _ = ‖(B (qDampedMobiusPartial ε N) - qDampedMobiusSmoothed ε) +
        (qDampedMobiusSmoothed ε - B qOne)‖ := by congr 1; abel
    _ ≤ ‖B (qDampedMobiusPartial ε N) - qDampedMobiusSmoothed ε‖ +
        ‖qDampedMobiusSmoothed ε - B qOne‖ := norm_add_le _ _
    _ ≤ (N : ℝ) ^ (-ε) / ε + ε * ‖qLogEnvelope‖ := add_le_add ht hc
    _ = _ := add_comm _ _

/-- Any finite cutoff schedule meeting the explicit scalar budget realizes
the reciprocal strong approximation; unsmoothed energy remains separate. -/
theorem qDampedMobiusPartial_reciprocal_tendsto (ε : ℕ → ℝ) (N : ℕ → ℕ)
    (hε : ∀ j, 0 < ε j) (hN : ∀ j, 1 ≤ N j)
    (hzero : Tendsto ε atTop (𝓝 0))
    (htail : Tendsto (fun j => (N j : ℝ) ^ (-(ε j)) / ε j) atTop (𝓝 0)) :
    Tendsto (fun j => B (qDampedMobiusPartial (ε j) (N j))) atTop (𝓝 (B qOne)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hu : Tendsto (fun j => ε j * ‖qLogEnvelope‖ +
      (N j : ℝ) ^ (-(ε j)) / ε j) atTop (𝓝 0) := by
    simpa only [zero_mul, zero_add] using (hzero.mul_const ‖qLogEnvelope‖).add htail
  apply squeeze_zero (fun _ => norm_nonneg _) _ hu
  intro j
  simpa only [map_sub] using qDampedMobiusPartial_reciprocal_error_le (hε j) (hN j)

end RiemannResearch.RH.DampedMobiusSmoothedSeries
