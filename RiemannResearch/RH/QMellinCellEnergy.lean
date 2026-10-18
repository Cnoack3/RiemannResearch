/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.MellinModeEnergyBounds
import RiemannResearch.RH.WeightedPowerCellMass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complete Q Mellin-cell energy and its positive metric correction

Source: the discrete Q-witness refinement recorded in
`BurnolQWitnessRefinement20261018.md`, motivated by Burnol (2001),
arXiv:math/0103058v2; actual cell estimates use `MellinModeEnergyBounds`.

The physical coordinate is `n + 1`. The actual Pareto-mode energy decomposes
as the actual Q difference energy plus a nonnegative, summable correction.
No zeta-zero hypothesis or RH assumption is used.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace RiemannResearch.RH.QMellinCell

open RiemannResearch.RH.Pareto
open RiemannResearch.RH.Pareto.SpectralObstruction

abbrev cellDifference (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 1) ^ (-s) - ((n : ℂ) + 2) ^ (-s)

def qMellinCellEnergy (s : ℂ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ 2 *
    ‖((n : ℂ) + 1) ^ (-s) - ((n : ℂ) + 2) ^ (-s)‖ ^ 2

def qMellinCellCorrection (s : ℂ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) *
    ‖((n : ℂ) + 1) ^ (-s) - ((n : ℂ) + 2) ^ (-s)‖ ^ 2

theorem qMellinCellEnergy_nonneg (s : ℂ) (n : ℕ) :
    0 ≤ qMellinCellEnergy s n := by
  unfold qMellinCellEnergy
  positivity

theorem qMellinCellCorrection_nonneg (s : ℂ) (n : ℕ) :
    0 ≤ qMellinCellCorrection s n := by
  unfold qMellinCellCorrection
  positivity

/-- Exact per-cell metric identity, retaining its nonnegative correction. -/
theorem pareto_cell_energy_eq (s : ℂ) (n : ℕ) :
    paretoWeight n * ‖mellinMode s n‖ ^ 2 =
      qMellinCellEnergy s n + qMellinCellCorrection s n := by
  have hc : ((n : ℂ) + 1) * ((n : ℂ) + 2) =
      ((((n : ℝ) + 1) * ((n : ℝ) + 2) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [mellinMode, norm_mul, hc, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  simp only [paretoWeight, qMellinCellEnergy, qMellinCellCorrection]
  field_simp [show (n : ℝ) + 1 ≠ 0 by positivity,
    show (n : ℝ) + 2 ≠ 0 by positivity]
  <;> ring

theorem qMellinCellEnergy_le_pareto (s : ℂ) (n : ℕ) :
    qMellinCellEnergy s n ≤ paretoWeight n * ‖mellinMode s n‖ ^ 2 := by
  rw [pareto_cell_energy_eq]
  exact le_add_of_nonneg_right (qMellinCellCorrection_nonneg s n)

theorem qMellinCellCorrection_le_pareto (s : ℂ) (n : ℕ) :
    qMellinCellCorrection s n ≤ paretoWeight n * ‖mellinMode s n‖ ^ 2 := by
  rw [pareto_cell_energy_eq]
  exact le_add_of_nonneg_left (qMellinCellEnergy_nonneg s n)

theorem qMellinCellEnergy_summable (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    Summable (qMellinCellEnergy s) := by
  exact Summable.of_nonneg_of_le (qMellinCellEnergy_nonneg s)
    (qMellinCellEnergy_le_pareto s) (mellinMode_energy_summable s hs)

theorem qMellinCellCorrection_summable (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    Summable (qMellinCellCorrection s) := by
  exact Summable.of_nonneg_of_le (qMellinCellCorrection_nonneg s)
    (qMellinCellCorrection_le_pareto s) (mellinMode_energy_summable s hs)

/-- The complete infinite P energy is Q energy plus its entire correction. -/
theorem pareto_energy_eq_q_add_correction (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (∑' n : ℕ, paretoWeight n * ‖mellinMode s n‖ ^ 2) =
      (∑' n : ℕ, qMellinCellEnergy s n) +
        ∑' n : ℕ, qMellinCellCorrection s n := by
  calc
    _ = ∑' n : ℕ, (qMellinCellEnergy s n + qMellinCellCorrection s n) :=
      tsum_congr (pareto_cell_energy_eq s)
    _ = _ := (qMellinCellEnergy_summable s hs).tsum_add
      (qMellinCellCorrection_summable s hs)

theorem q_energy_add_correction_le (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (∑' n : ℕ, qMellinCellEnergy s n) +
        (∑' n : ℕ, qMellinCellCorrection s n) ≤
      ‖s‖ ^ 2 / (2 * s.re - 1) := by
  rw [← pareto_energy_eq_q_add_correction s hs]
  exact mellinMode_energy_le s hs

@[simp] theorem qMellinCellCorrection_zero (s : ℂ) :
    qMellinCellCorrection s 0 = ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 := by
  simp [qMellinCellCorrection]

theorem first_cell_le_correction (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 ≤ ∑' n : ℕ, qMellinCellCorrection s n := by
  have h := (qMellinCellCorrection_summable s hs).le_tsum 0
    (fun n _ => qMellinCellCorrection_nonneg s n)
  simpa only [qMellinCellCorrection_zero] using h

/-- An explicit improvement, obtained while retaining the full infinite energy. -/
theorem q_energy_le_sub_first_cell (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (∑' n : ℕ, qMellinCellEnergy s n) ≤
      ‖s‖ ^ 2 / (2 * s.re - 1) - ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 := by
  have he := q_energy_add_correction_le s hs
  have hc := first_cell_le_correction s hs
  linarith

theorem first_cell_correction_pos (s : ℂ) (hs : 0 < s.re) :
    0 < ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 := by
  have hn : ‖(2 : ℂ) ^ (-s)‖ < 1 := by
    change ‖((2 : ℝ) : ℂ) ^ (-s)‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2),
      Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hne : 1 - (2 : ℂ) ^ (-s) ≠ 0 := by
    intro he
    have hp : (2 : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp he).symm
    rw [hp, norm_one] at hn
    exact (lt_irrefl (1 : ℝ)) hn
  exact pow_pos (norm_pos_iff.mpr hne) 2

theorem q_energy_lt_integral_bound (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (∑' n : ℕ, qMellinCellEnergy s n) < ‖s‖ ^ 2 / (2 * s.re - 1) := by
  have he := q_energy_le_sub_first_cell s hs
  have hp := first_cell_correction_pos s (by linarith)
  linarith

/-- Exact cell ratio, before any estimate or summation. -/
theorem qMellinCellEnergy_eq_ratio_pareto (s : ℂ) (n : ℕ) :
    qMellinCellEnergy s n =
      (((n : ℝ) + 1) / ((n : ℝ) + 2)) *
        (paretoWeight n * ‖mellinMode s n‖ ^ 2) := by
  rw [pareto_cell_energy_eq]
  unfold qMellinCellEnergy qMellinCellCorrection
  field_simp [show (n : ℝ) + 2 ≠ 0 by positivity]
  <;> ring

/-- The sharper actual cell majorant needed by the reciprocal Abel summation. -/
theorem qMellinCellEnergy_le_weighted_powerCellMass (s : ℂ)
    (hs : 0 < s.re) (n : ℕ) :
    qMellinCellEnergy s n ≤
      ‖s‖ ^ 2 * (((n : ℝ) + 1) / ((n : ℝ) + 2)) * powerCellMass s.re 1 n := by
  have hc : paretoWeight n * ‖mellinMode s n‖ ^ 2 ≤
      ‖s‖ ^ 2 * powerCellMass s.re 1 n := by
    simpa only [powerCellMass,
      show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
      using mellinMode_energy_cell_le s hs n
  rw [qMellinCellEnergy_eq_ratio_pareto]
  calc
    _ ≤ (((n : ℝ) + 1) / ((n : ℝ) + 2)) *
        (‖s‖ ^ 2 * powerCellMass s.re 1 n) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

/-- Summing the exact reciprocal-cell weights sharpens the continuous bound. -/
theorem q_energy_le_envelope (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (∑' n, qMellinCellEnergy s n) ≤
      ‖s‖ ^ 2 * reciprocalPowerEnvelope s.re / (2 * s.re - 1) := by
  have hc (n : ℕ) : qMellinCellEnergy s n ≤
      ‖s‖ ^ 2 * weightedPowerCellMass s.re n := by
    simpa only [weightedPowerCellMass,
      RiemannResearch.Analysis.ReciprocalCellAbel.boundaryFactor,
      Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring,
      mul_assoc] using qMellinCellEnergy_le_weighted_powerCellMass s (by linarith) n
  have h := Summable.tsum_le_tsum hc (qMellinCellEnergy_summable s hs)
    ((weightedPowerCellMass_summable s.re hs).mul_left (‖s‖ ^ 2))
  rw [tsum_mul_left, weightedPowerCellMass_tsum s.re hs] at h
  simpa only [mul_div_assoc] using h

/-- The actual nonnegative gap in the weighted cell estimate. -/
def qMellinCellSlack (s : ℂ) (n : ℕ) : ℝ :=
  ‖s‖ ^ 2 * weightedPowerCellMass s.re n - qMellinCellEnergy s n

theorem qMellinCellSlack_nonneg (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    0 ≤ qMellinCellSlack s n := by
  apply sub_nonneg.mpr
  simpa only [weightedPowerCellMass,
    RiemannResearch.Analysis.ReciprocalCellAbel.boundaryFactor,
    Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring,
    mul_assoc] using qMellinCellEnergy_le_weighted_powerCellMass s hs n

theorem qMellinCellSlack_summable (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    Summable (qMellinCellSlack s) :=
  ((weightedPowerCellMass_summable s.re hs).mul_left (‖s‖ ^ 2)).sub
    (qMellinCellEnergy_summable s hs)

/-- Exact energy identity, including the entire Cauchy--Schwarz remainder. -/
theorem q_energy_add_slack_eq_envelope (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (∑' n, qMellinCellEnergy s n) + (∑' n, qMellinCellSlack s n) =
      ‖s‖ ^ 2 * reciprocalPowerEnvelope s.re / (2 * s.re - 1) := by
  rw [show (∑' n, qMellinCellSlack s n) =
    ‖s‖ ^ 2 * (∑' n, weightedPowerCellMass s.re n) -
      (∑' n, qMellinCellEnergy s n) by
    unfold qMellinCellSlack
    rw [Summable.tsum_sub ((weightedPowerCellMass_summable s.re hs).mul_left _)
      (qMellinCellEnergy_summable s hs), tsum_mul_left]]
  rw [weightedPowerCellMass_tsum s.re hs]
  ring

/-- Any finite prefix of the actual cell gap yields a certified refined envelope. -/
theorem q_energy_le_envelope_sub_slack (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (N : ℕ) :
    (∑' n, qMellinCellEnergy s n) ≤
      ‖s‖ ^ 2 * reciprocalPowerEnvelope s.re / (2 * s.re - 1) -
        ∑ n ∈ Finset.range N, qMellinCellSlack s n := by
  have he := q_energy_add_slack_eq_envelope s hs
  have hp := Summable.sum_le_tsum (Finset.range N)
    (fun n _ => qMellinCellSlack_nonneg s (by linarith) n)
    (qMellinCellSlack_summable s hs)
  linarith

end RiemannResearch.RH.QMellinCell
