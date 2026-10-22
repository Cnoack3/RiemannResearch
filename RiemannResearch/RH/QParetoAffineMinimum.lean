/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramAffineMinimum
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.RH.QMetricCorrectionBounds
import RiemannResearch.RH.QParetoGramComparison
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact stability of affine residual minima under the Q/P change of measure

Source: continuation of the user's QCanonicalCofinalGramResearch20261015
handoff. The proof uses the project's exact finite Gram completion and the
reciprocal metric correction, rather than a bound on coefficient masses.

The normal equations below are finite algebraic hypotheses. In the canonical
window application, actual inverse Gram matrices discharge both equations.
No arithmetic upper bound on the full minimum energy is proved here.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.QParetoAffineMinimum
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoMetric QMetricCorrectionBounds QParetoGramComparison
open RiemannResearch.Analysis.FiniteHilbertGram

variable {ι : Type*} [Fintype ι]

/-- The same affine coefficients are always synthesized in actual Q coordinates. -/
def affineVector (v : ι → QHilbert) (z : ι → ℝ) : QHilbert :=
  Fintype.linearCombination ℝ v (affineCoefficients z)

theorem toPareto_affineVector (v : ι → QHilbert) (z : ι → ℝ) :
    toPareto (affineVector v z) =
      Fintype.linearCombination ℝ (paretoFamily v) (affineCoefficients z) :=
  toPareto_synthesis _ _

theorem affineVector_sub (v : ι → QHilbert) (p q : ι → ℝ) :
    affineVector v p - affineVector v q =
      Fintype.linearCombination ℝ v (affineCoefficients p - affineCoefficients q) :=
  (map_sub (Fintype.linearCombination ℝ v) _ _).symm

variable [Nonempty ι]

/-- Exact Pythagoras for the P minimizer, evaluated at the Q minimizer. -/
theorem pareto_completion (v : ι → QHilbert) (p q : ι → ℝ)
    (hp : gram (paretoFamily v) p = fun _ => 1)
    (hq : gram v q = fun _ => 1) :
    ‖toPareto (affineVector v q)‖ ^ 2 =
      ‖toPareto (affineVector v p)‖ ^ 2 +
        ‖toPareto (affineVector v q - affineVector v p)‖ ^ 2 := by
  rw [affineVector_sub, toPareto_synthesis]
  simp only [affineVector, toPareto_synthesis]
  rw [affineCoefficients_energy _ _ hp]
  exact affineCoefficients_completion _ _ _ hp (affineCoefficients_sum _ _ hq)

/-- Exact Q Pythagoras, with the same signed displacement retained. -/
theorem q_completion (v : ι → QHilbert) (p q : ι → ℝ)
    (hp : gram (paretoFamily v) p = fun _ => 1)
    (hq : gram v q = fun _ => 1) :
    ‖affineVector v p‖ ^ 2 = ‖affineVector v q‖ ^ 2 +
      ‖affineVector v q - affineVector v p‖ ^ 2 := by
  rw [norm_sub_rev]
  change ‖Fintype.linearCombination ℝ v (affineCoefficients p)‖ ^ 2 =
    ‖Fintype.linearCombination ℝ v (affineCoefficients q)‖ ^ 2 +
      ‖Fintype.linearCombination ℝ v (affineCoefficients p) -
        Fintype.linearCombination ℝ v (affineCoefficients q)‖ ^ 2
  rw [affineCoefficients_energy _ _ hq]
  simpa only [map_sub] using
    affineCoefficients_completion v q (affineCoefficients p) hq
      (affineCoefficients_sum _ _ hp)

/-- All correction and displacement terms are retained in this equality. -/
theorem correction_balance (v : ι → QHilbert) (p q : ι → ℝ)
    (hp : gram (paretoFamily v) p = fun _ => 1)
    (hq : gram v q = fun _ => 1) :
    metricCorrection (affineVector v p) =
      metricCorrection (affineVector v q) +
        2 * ‖toPareto (affineVector v q - affineVector v p)‖ ^ 2 +
          metricCorrection (affineVector v q - affineVector v p) := by
  have hP := pareto_completion v p q hp hq
  have hQ := q_completion v p q hp hq
  have hx := norm_identity (affineVector v p)
  have hy := norm_identity (affineVector v q)
  have he := norm_identity (affineVector v q - affineVector v p)
  have hQz := congrArg (fun E : ℝ => zetaTwo * E) hQ
  rw [mul_add] at hQz
  linarith only [hP, hQz, hx, hy, he]

/-- The gap retains the correction at the Q minimizer and the complete
P displacement energy as separate nonnegative terms. -/
theorem minimum_energy_gap_identity (v : ι → QHilbert) (p q : ι → ℝ)
    (hp : gram (paretoFamily v) p = fun _ => 1)
    (hq : gram v q = fun _ => 1) :
    zetaTwo * ‖affineVector v q‖ ^ 2 - ‖toPareto (affineVector v p)‖ ^ 2 =
      metricCorrection (affineVector v q) +
        ‖toPareto (affineVector v q - affineVector v p)‖ ^ 2 := by
  rw [norm_identity, pareto_completion v p q hp hq]
  ring

/-- The two actual minima differ by at most the correction at the P minimizer. -/
theorem minimum_energy_gap (v : ι → QHilbert) (p q : ι → ℝ)
    (hp : gram (paretoFamily v) p = fun _ => 1)
    (hq : gram v q = fun _ => 1) :
    0 ≤ zetaTwo * ‖affineVector v q‖ ^ 2 -
        ‖toPareto (affineVector v p)‖ ^ 2 ∧
      zetaTwo * ‖affineVector v q‖ ^ 2 -
        ‖toPareto (affineVector v p)‖ ^ 2 ≤ metricCorrection (affineVector v p) := by
  have hP := pareto_completion v p q hp hq
  have hQ := q_completion v p q hp hq
  have hx := norm_identity (affineVector v p)
  have hy := norm_identity (affineVector v q)
  have hQz := congrArg (fun E : ℝ => zetaTwo * E) hQ
  rw [mul_add] at hQz
  constructor
  · nlinarith only [hP, hy, metricCorrection_nonneg (affineVector v q),
      sq_nonneg ‖toPareto (affineVector v q - affineVector v p)‖]
  · linarith only [hQz, hx, mul_nonneg zetaTwo_pos.le
      (sq_nonneg ‖affineVector v q - affineVector v p‖)]

/-- The stronger reciprocal mixed estimate gives a second reciprocal
factor in squared displacement. No coefficient norm is assumed. -/
theorem displacement_sq_le_correction (v : ι → QHilbert) (p q : ι → ℝ)
    (hp : gram (paretoFamily v) p = fun _ => 1)
    (hq : gram v q = fun _ => 1) (H : ℕ)
    (hhead : ∀ i k, 0 < k → k ≤ H → qSequence (v i) k = 0) :
    ‖toPareto (affineVector v q - affineVector v p)‖ ^ 2 ≤
      metricCorrection (affineVector v p) / ((H : ℝ) + 1) := by
  let x := affineVector v p
  let y := affineVector v q
  let e := y - x
  have hxhead : ∀ k, 0 < k → k ≤ H → qSequence x k = 0 :=
    synthesis_head_zero v (affineCoefficients p) H hhead
  have hbalance := correction_balance v p q hp hq
  change metricCorrection x =
    metricCorrection y + 2 * ‖toPareto e‖ ^ 2 + metricCorrection e at hbalance
  have hadd := metricCorrection_add x e
  have hxe : x + e = y := by dsimp [e]; abel
  rw [hxe] at hadd
  have hs := metricPairing_symmetric x e
  have hpair : metricPairing e x =
      -(‖toPareto e‖ ^ 2 + metricCorrection e) := by
    nlinarith only [hbalance, hadd, hs]
  have hb := metricPairing_sq_le_test_norm e x H hxhead
  rw [hpair, neg_sq] at hb
  have hb' : (‖toPareto e‖ ^ 2 + metricCorrection e) ^ 2 ≤
      ‖toPareto e‖ ^ 2 * (metricCorrection x / ((H : ℝ) + 1)) :=
    hb.trans_eq (by ring)
  change ‖toPareto e‖ ^ 2 ≤ metricCorrection x / ((H : ℝ) + 1)
  have hR := metricCorrection_nonneg e
  have hE := sq_nonneg ‖toPareto e‖
  have hB : 0 ≤ metricCorrection x / ((H : ℝ) + 1) :=
    div_nonneg (metricCorrection_nonneg x) (by positivity)
  by_contra hnot
  have hlt : metricCorrection x / ((H : ℝ) + 1) < ‖toPareto e‖ ^ 2 :=
    lt_of_not_ge hnot
  have hmul := mul_lt_mul_of_pos_left hlt (lt_of_le_of_lt hB hlt)
  nlinarith only [hb', hmul, mul_nonneg hE hR, sq_nonneg (metricCorrection e)]

theorem displacement_sq_le_pareto_energy (v : ι → QHilbert) (p q : ι → ℝ)
    (hp : gram (paretoFamily v) p = fun _ => 1)
    (hq : gram v q = fun _ => 1) (H : ℕ)
    (hhead : ∀ i k, 0 < k → k ≤ H → qSequence (v i) k = 0) :
    ‖toPareto (affineVector v q - affineVector v p)‖ ^ 2 ≤
      ‖toPareto (affineVector v p)‖ ^ 2 / ((H : ℝ) + 1) ^ 2 := by
  refine (displacement_sq_le_correction v p q hp hq H hhead).trans ?_
  have hc := metricCorrection_le_of_head_zero (affineVector v p) H
    (synthesis_head_zero v (affineCoefficients p) H hhead)
  exact (div_le_div_of_nonneg_right hc (by positivity)).trans_eq
    (by simp only [div_div, pow_two])

/-- Any one residual in the family is an admissible affine competitor. -/
theorem pareto_minimum_le_vertex (v : ι → QHilbert) (p : ι → ℝ)
    (hp : gram (paretoFamily v) p = fun _ => 1) (i : ι) :
    ‖toPareto (affineVector v p)‖ ^ 2 ≤ ‖toPareto (v i)‖ ^ 2 := by
  classical
  let c : ι → ℝ := fun j => if j = i then 1 else 0
  have hc : ∑ j, c j = 1 := by simp [c]
  have he : Fintype.linearCombination ℝ (paretoFamily v) c = toPareto (v i) := by
    simp [Fintype.linearCombination_apply, c, paretoFamily]
  rw [toPareto_affineVector, affineCoefficients_energy _ _ hp]
  exact (affineCoefficients_isLeast _ _ hp).2 ⟨c, hc, congrArg (fun x => ‖x‖ ^ 2) he⟩

end RiemannResearch.RH.QParetoAffineMinimum
