/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QMellinCellEnergy
import RiemannResearch.RH.QMellinTransfer
import RiemannResearch.Analysis.MellinStepSeries
import RiemannResearch.Analysis.WeightedComplexPairing

/-!
# The actual discrete Q Mellin witness

Source: the discrete Q-witness refinement recorded in
`BurnolQWitnessRefinement20261018.md`, motivated by Burnol (2001),
arXiv:math/0103058v2. No historical novelty is claimed.

The complete signed first-difference series represents `s * qMellin f s`.
Its convergent weighted dual energy bounds the functional on the actual
inverse-square Hilbert space. A zeta zero then separates every finite legal
residue approximation from the constant target.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QMellinWitness
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QMellinTransfer
open QCovarianceInverse QMellinCell
open RiemannResearch.Analysis.Cesaro

/-- The normalization includes exactly one factor of zeta(2). -/
theorem dual_cell_eq (s : ℂ) (n : ℕ) :
    ‖mellinFirst s (n + 1)‖ ^ 2 / qWeight n =
      zetaTwo * qMellinCellEnergy s n := by
  simp only [mellinFirst, qWeight, positiveQWeight, qMellinCellEnergy,
    Nat.cast_add, Nat.cast_one]
  rw [show (n : ℂ) + 1 + 1 = (n : ℂ) + 2 by ring]
  simp only [div_eq_mul_inv, one_mul, inv_inv]
  ring

/-- Ordinary convergence of the complete discrete witness, with its actual value. -/
theorem qMellin_hasSum (f : QHilbert) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    HasSum (fun n => mellinFirst s (n + 1) * (qSequence f (n + 1) : ℂ))
      (s * qMellin f s) := by
  simpa only [toPareto_sequence, qMellin] using
    hasSum_first_mellin_pairing (toPareto f) s hs

/-- Cauchy--Schwarz with the full discrete dual energy, including every tail cell. -/
theorem qMellin_norm_sq_le_discrete (f : QHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    ‖s * qMellin f s‖ ^ 2 ≤
      (zetaTwo * ∑' n, qMellinCellEnergy s n) * ‖f‖ ^ 2 := by
  have hb : Summable (fun n => ‖mellinFirst s (n + 1)‖ ^ 2 / qWeight n) := by
    simpa only [dual_cell_eq] using (qMellinCellEnergy_summable s hs).mul_left zetaTwo
  have hM : Summable (fun n => qWeight n * ‖(qSequence f (n + 1) : ℂ)‖ ^ 2) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs, qWeight,
      qSequence_weighted_square] using qCoordinate_square_summable f
  have h := RiemannResearch.Analysis.WeightedPairing.pairing_norm_sq_le
    qWeight qWeight_pos (fun n => mellinFirst s (n + 1))
    (fun n => (qSequence f (n + 1) : ℂ)) hb hM
  rw [(qMellin_hasSum f s hs).tsum_eq] at h
  simp_rw [dual_cell_eq] at h
  rw [tsum_mul_left] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    sq_abs, qWeight, qSequence_weighted_square, ← qNorm_sq] using h

/-- The complete witness energy is positive, as certified by its value on the target. -/
theorem qMellin_energy_pos (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    0 < ∑' n, qMellinCellEnergy s n := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h := qMellin_norm_sq_le_discrete qOne s hs
  rw [qMellin_one s hs, mul_one_div_cancel hs0, norm_one, one_pow, qOne_norm_sq,
    mul_one] at h
  have hz : 0 < zetaTwo * ∑' n, qMellinCellEnergy s n := lt_of_lt_of_le zero_lt_one h
  by_contra hn
  have hh := mul_nonpos_of_nonneg_of_nonpos zetaTwo_pos.le (le_of_not_gt hn)
  linarith

/-- A zeta zero gives the reciprocal of the actual discrete witness energy. -/
theorem legal_error_lower_discrete {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) (c : ι → ℝ)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    1 / (zetaTwo * ∑' n, qMellinCellEnergy s n) ≤
      ‖qOne - qSynthesis d c‖ ^ 2 := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h := qMellin_norm_sq_le_discrete (qOne - qSynthesis d c) s hs
  rw [qMellin_error_at_zero d hd c s hs hs1 hz, mul_one_div_cancel hs0,
    norm_one, one_pow] at h
  apply (div_le_iff₀ (mul_pos zetaTwo_pos (qMellin_energy_pos s hs))).2
  nlinarith only [h]

/-- Any certified upper bound on the complete witness energy gives an error bound. -/
theorem legal_error_lower_of_energy_bound {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) (c : ι → ℝ)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (U : ℝ) (hU : (∑' n, qMellinCellEnergy s n) ≤ U) :
    1 / (zetaTwo * U) ≤ ‖qOne - qSynthesis d c‖ ^ 2 := by
  apply le_trans _ (legal_error_lower_discrete d hd c s hs hs1 hz)
  exact one_div_le_one_div_of_le (mul_pos zetaTwo_pos (qMellin_energy_pos s hs))
    (mul_le_mul_of_nonneg_left hU zetaTwo_pos.le)

/-- The reciprocal-cell factor strictly strengthens the earlier global transfer bound. -/
theorem legal_error_lower_envelope {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) (c : ι → ℝ)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (2 * s.re - 1) /
      (zetaTwo * ‖s‖ ^ 2 * Pareto.SpectralObstruction.reciprocalPowerEnvelope s.re) ≤
        ‖qOne - qSynthesis d c‖ ^ 2 := by
  have h := legal_error_lower_of_energy_bound d hd c s hs hs1 hz
    _ (q_energy_le_envelope s hs)
  convert h using 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
  ring

/-- An exact finite prefix of the actual cell slack strengthens the B-factor bound. -/
theorem legal_error_lower_envelope_sub_slack {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) (c : ι → ℝ)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (N : ℕ) :
    1 / (zetaTwo *
      (‖s‖ ^ 2 * Pareto.SpectralObstruction.reciprocalPowerEnvelope s.re /
        (2 * s.re - 1) - ∑ n ∈ Finset.range N, qMellinCellSlack s n)) ≤
      ‖qOne - qSynthesis d c‖ ^ 2 :=
  legal_error_lower_of_energy_bound d hd c s hs hs1 hz _
    (q_energy_le_envelope_sub_slack s hs N)

/-- Strict improvement is quantitative and requires no unproved asymptotic input. -/
theorem old_bound_lt_envelope_bound (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (2 * s.re - 1) / (zetaTwo * ‖s‖ ^ 2) <
      (2 * s.re - 1) /
        (zetaTwo * ‖s‖ ^ 2 * Pareto.SpectralObstruction.reciprocalPowerEnvelope s.re) := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hp : 0 < zetaTwo * ‖s‖ ^ 2 := mul_pos zetaTwo_pos (pow_pos (norm_pos_iff.mpr hs0) 2)
  have hB := Pareto.SpectralObstruction.reciprocalPowerEnvelope_pos s.re hs
  have hB1 := Pareto.SpectralObstruction.reciprocalPowerEnvelope_lt_one s.re hs
  apply div_lt_div_of_pos_left (by linarith) (mul_pos hp hB)
  nlinarith

end RiemannResearch.RH.QMellinWitness
