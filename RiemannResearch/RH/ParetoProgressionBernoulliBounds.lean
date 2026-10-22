/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoProgressionDigamma
import RiemannResearch.RH.DigammaBernoulliDifferences
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Head-retaining Bernoulli enclosures for complete Pareto CRT weights

The exact first physical-site mass is retained. Only the complete remaining
progression mass is approximated, through the actual pole-removed digamma
difference. The signed error is a single complete endpoint-defect difference,
whose all-order bound preserves the first-omitted inverse-power cancellation.

Source: user-provided weighted CRT continuation, 7 October 2026; the actual
digamma progression identity is proved in `ParetoProgressionDigamma` and
the strict alternating remainder difference is proved in
`DigammaBernoulliDifferences`.
-/

namespace RiemannResearch.RH.ParetoProgressionBernoulliBounds

noncomputable section

open RiemannResearch.RH.Pareto
open RiemannResearch.RH.DigammaBernoulliCells
open RiemannResearch.RH.DigammaBernoulliRemainderEstimates
open RiemannResearch.RH.DigammaBernoulliSignedRemainder
open RiemannResearch.RH.DigammaBernoulliDifferences

/-- The physical head remains exact at every Bernoulli truncation order. -/
def progressionBernoulliApprox (Q r N : ℕ) : ℝ :=
  positiveWeight r + 1 / (Q : ℝ) *
    ((Real.log (1 + ((r : ℝ) + 1) / Q) -
        1 / (2 * (1 + ((r : ℝ) + 1) / Q)) -
        evenBernoulliPowerSum N (1 + ((r : ℝ) + 1) / Q)) -
      (Real.log (1 + (r : ℝ) / Q) -
        1 / (2 * (1 + (r : ℝ) / Q)) -
        evenBernoulliPowerSum N (1 + (r : ℝ) / Q)))

/-- The next correction is exactly the first-omitted inverse-power difference. -/
theorem progressionBernoulliApprox_succ_sub (Q r N : ℕ) :
    progressionBernoulliApprox Q r (N + 1) - progressionBernoulliApprox Q r N =
      bernoulliCoefficient (2 * N + 2) / (Q : ℝ) *
        (((1 + (r : ℝ) / Q)⁻¹) ^ (2 * N + 2) -
          ((1 + ((r : ℝ) + 1) / Q)⁻¹) ^ (2 * N + 2)) := by
  simp only [progressionBernoulliApprox, evenBernoulliPowerSum,
    Finset.sum_range_succ]
  ring

/-- Complete exact progression error, before any sign or magnitude estimate. -/
theorem progressionWeight_sub_bernoulliApprox_exact (Q r N : ℕ)
    (hQ : 0 < Q) (hr : 0 < r) (hrQ : r ≤ Q) :
    progressionWeight Q r - progressionBernoulliApprox Q r N =
      -(evenDigammaError N (1 + (r : ℝ) / Q) -
        evenDigammaError N (1 + ((r : ℝ) + 1) / Q)) / (Q : ℝ) := by
  rw [progressionWeight_eq_head_digamma Q r hQ hr hrQ]
  unfold progressionBernoulliApprox evenDigammaError
  ring

/-- Every truncation has a strict alternating error bounded by one omitted
inverse-power difference, rather than two independent endpoint estimates. -/
theorem progressionWeight_sub_bernoulliApprox_strict_signed_bound
    (Q r N : ℕ) (hQ : 0 < Q) (hr : 0 < r) (hrQ : r ≤ Q) :
    0 < (-1 : ℝ) ^ N *
      (progressionWeight Q r - progressionBernoulliApprox Q r N) ∧
    (-1 : ℝ) ^ N *
      (progressionWeight Q r - progressionBernoulliApprox Q r N) <
      |bernoulliCoefficient (2 * N + 2)| / (Q : ℝ) *
        (((1 + (r : ℝ) / Q)⁻¹) ^ (2 * N + 2) -
          ((1 + ((r : ℝ) + 1) / Q)⁻¹) ^ (2 * N + 2)) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hx : 0 < 1 + (r : ℝ) / Q := by positivity
  have hxy : 1 + (r : ℝ) / Q < 1 + ((r : ℝ) + 1) / Q := by
    have hh : (r : ℝ) / Q < ((r : ℝ) + 1) / Q :=
      (div_lt_div_iff_of_pos_right hQr).mpr (by linarith)
    linarith
  have hb := evenDigammaError_sub_strict_signed_bound hx hxy N
  have he : (-1 : ℝ) ^ N *
      (progressionWeight Q r - progressionBernoulliApprox Q r N) =
      ((-1 : ℝ) ^ (N + 1) *
        (evenDigammaError N (1 + (r : ℝ) / Q) -
          evenDigammaError N (1 + ((r : ℝ) + 1) / Q))) / (Q : ℝ) := by
    rw [progressionWeight_sub_bernoulliApprox_exact Q r N hQ hr hrQ, pow_succ]
    ring
  rw [he]
  constructor
  · exact div_pos hb.1 hQr
  · have hd := (div_lt_div_iff_of_pos_right hQr).mpr hb.2
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hd

/-- The actual error is nonzero and its absolute bound retains the omitted
inverse powers inside their difference. -/
theorem progressionWeight_sub_bernoulliApprox_strict_absolute_bound
    (Q r N : ℕ) (hQ : 0 < Q) (hr : 0 < r) (hrQ : r ≤ Q) :
    0 < |progressionWeight Q r - progressionBernoulliApprox Q r N| ∧
    |progressionWeight Q r - progressionBernoulliApprox Q r N| <
      |bernoulliCoefficient (2 * N + 2)| / (Q : ℝ) *
        (((1 + (r : ℝ) / Q)⁻¹) ^ (2 * N + 2) -
          ((1 + ((r : ℝ) + 1) / Q)⁻¹) ^ (2 * N + 2)) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hx : 0 < 1 + (r : ℝ) / Q := by positivity
  have hxy : 1 + (r : ℝ) / Q < 1 + ((r : ℝ) + 1) / Q := by
    have hh : (r : ℝ) / Q < ((r : ℝ) + 1) / Q :=
      (div_lt_div_iff_of_pos_right hQr).mpr (by linarith)
    linarith
  have hb := evenDigammaError_sub_strict_absolute_bound hx hxy N
  rw [progressionWeight_sub_bernoulliApprox_exact Q r N hQ hr hrQ,
    abs_div, abs_neg, abs_of_pos hQr]
  constructor
  · exact div_pos hb.1 hQr
  · have hd := (div_lt_div_iff_of_pos_right hQr).mpr hb.2
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hd

/-- Even orders give certified strict lower bounds for the complete weight. -/
theorem progressionBernoulliApprox_even_lt_weight (Q r N : ℕ)
    (hQ : 0 < Q) (hr : 0 < r) (hrQ : r ≤ Q) :
    progressionBernoulliApprox Q r (2 * N) < progressionWeight Q r := by
  have hb := (progressionWeight_sub_bernoulliApprox_strict_signed_bound
    Q r (2 * N) hQ hr hrQ).1
  have he : (-1 : ℝ) ^ (2 * N) = 1 := by
    rw [pow_mul]
    norm_num
  rw [he, one_mul] at hb
  exact sub_pos.mp hb

/-- Odd orders give certified strict upper bounds for the complete weight. -/
theorem progressionWeight_lt_bernoulliApprox_odd (Q r N : ℕ)
    (hQ : 0 < Q) (hr : 0 < r) (hrQ : r ≤ Q) :
    progressionWeight Q r < progressionBernoulliApprox Q r (2 * N + 1) := by
  have hb := (progressionWeight_sub_bernoulliApprox_strict_signed_bound
    Q r (2 * N + 1) hQ hr hrQ).1
  have he : (-1 : ℝ) ^ (2 * N + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [he] at hb
  linarith

end
end RiemannResearch.RH.ParetoProgressionBernoulliBounds
