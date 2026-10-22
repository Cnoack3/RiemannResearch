/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ParetoMellinFunctional
import RiemannResearch.RH.ParetoAtomMellinSignature
import RiemannResearch.RH.QCovarianceInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Continuous physical Mellin and zeta obstructions in Q

Source: the checked Pareto Mellin functional and normalized-atom signature,
transported for the user's Pareto-to-Q request, 15 October 2026.
The same physical step-function integral is retained. This is not a claim
that a Q expectation and a Pareto expectation are equal.

The exact metric correction sharpens the transferred Mellin estimate and
the zero obstruction. The latter remains an obstruction conditional on an
off-line zero; no zero or approximation hypothesis is asserted.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.QMellinTransfer
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoMetric QCovarianceInverse

/-- Mellin transform of the same physical step sequence in the Q realization. -/
def qMellin (f : QHilbert) (s : ℂ) : ℂ := paretoMellin (toPareto f) s

theorem qMellin_eq_step_integral (f : QHilbert) (s : ℂ) :
    qMellin f s =
      ∫ x in Ioi (1 : ℝ), (qSequence f ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1) := by
  rw [qMellin, paretoMellin_eq_step_integral, toPareto_sequence]

def qMellinContinuous (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) : QHilbert →L[ℝ] ℂ :=
  (paretoMellinContinuous s hs).comp toParetoCLM

@[simp] theorem qMellinContinuous_apply (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (f : QHilbert) : qMellinContinuous s hs f = qMellin f s := rfl

theorem qMellin_add (f g : QHilbert) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    qMellin (f + g) s = qMellin f s + qMellin g s :=
  (qMellinContinuous s hs).map_add f g

theorem qMellin_smul (c : ℝ) (f : QHilbert) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    qMellin (c • f) s = c • qMellin f s :=
  (qMellinContinuous s hs).map_smul c f

/-- The complete positive correction is subtracted before taking the estimate. -/
theorem qMellin_norm_sq_le_exact (f : QHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    ‖qMellin f s‖ ^ 2 ≤
      (zetaTwo * ‖f‖ ^ 2 - metricCorrection f) / (2 * s.re - 1) := by
  have h := paretoMellin_norm_sq_le (toPareto f) s hs
  rw [norm_identity]
  simpa only [add_sub_cancel_right, qMellin] using h

theorem qMellin_norm_sq_le (f : QHilbert) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    ‖qMellin f s‖ ^ 2 ≤ zetaTwo * ‖f‖ ^ 2 / (2 * s.re - 1) := by
  exact (qMellin_norm_sq_le_exact f s hs).trans
    (div_le_div_of_nonneg_right (sub_le_self _ (metricCorrection_nonneg _))
      (by linarith))

theorem qMellin_one (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    qMellin qOne s = 1 / s := by
  rw [qMellin, toPareto_qOne, paretoMellin_one s hs]

/-- The legal normalized residue keeps its exact zeta signature. -/
theorem qMellin_residue_zeta (d : ℕ) (hd : 0 < d) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    qMellin (qResidue d) s =
      riemannZeta s / s * ((1 / (d : ℂ)) - (d : ℂ) ^ (-s)) := by
  rw [qMellin, toPareto_qResidue d hd, BaezDuarte.residueVector, dif_pos hd]
  exact ParetoAtomMellinSignature.paretoMellin_normalizedResidue_zeta d hd s hs hs1

theorem qMellin_residue_zero (d : ℕ) (hd : 0 < d) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    qMellin (qResidue d) s = 0 := by
  rw [qMellin_residue_zeta d hd s hs hs1, hz, zero_div, zero_mul]

theorem qMellin_synthesis {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (c : ι → ℝ) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    qMellin (qSynthesis d c) s = ∑ i, c i • qMellin (qResidue (d i)) s := by
  change qMellinContinuous s hs (∑ i, c i • qResidue (d i)) = _
  simp only [map_sum, map_smul, qMellinContinuous_apply]

theorem qMellin_error_at_zero {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) (c : ι → ℝ)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    qMellin (qOne - qSynthesis d c) s = 1 / s := by
  change qMellinContinuous s hs (qOne - qSynthesis d c) = _
  rw [map_sub]
  change qMellin qOne s - qMellin (qSynthesis d c) s = _
  rw [qMellin_one s hs, qMellin_synthesis d c s hs]
  simp only [qMellin_residue_zero _ (hd _) s (by linarith) hs1 hz,
    smul_zero, Finset.sum_const_zero, sub_zero]

/-- A zero obstruction plus the full positive correction, stronger than
merely transferring a global norm-comparison constant. -/
theorem legal_error_lower_with_correction {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) (c : ι → ℝ)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (2 * s.re - 1) / ‖s‖ ^ 2 + metricCorrection (qOne - qSynthesis d c) ≤
      zetaTwo * ‖qOne - qSynthesis d c‖ ^ 2 := by
  have h := qMellin_norm_sq_le_exact (qOne - qSynthesis d c) s hs
  rw [qMellin_error_at_zero d hd c s hs hs1 hz] at h
  have hdpos : 0 < 2 * s.re - 1 := by linarith
  have hh := (le_div_iff₀ hdpos).mp h
  have he : ‖1 / s‖ ^ 2 * (2 * s.re - 1) = (2 * s.re - 1) / ‖s‖ ^ 2 := by
    rw [norm_div, norm_one, div_pow, one_pow]
    ring
  rw [he] at hh
  linarith only [hh]

theorem legal_error_lower {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) (c : ι → ℝ)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (2 * s.re - 1) / (zetaTwo * ‖s‖ ^ 2) ≤ ‖qOne - qSynthesis d c‖ ^ 2 := by
  have h := legal_error_lower_with_correction d hd c s hs hs1 hz
  have hc := metricCorrection_nonneg (qOne - qSynthesis d c)
  rw [show (2 * s.re - 1) / (zetaTwo * ‖s‖ ^ 2) =
    ((2 * s.re - 1) / ‖s‖ ^ 2) / zetaTwo by ring]
  apply (div_le_iff₀ zetaTwo_pos).mpr
  nlinarith only [h, hc]

end RiemannResearch.RH.QMellinTransfer
