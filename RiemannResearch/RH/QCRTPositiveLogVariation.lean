/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PositiveLogVariation
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import RiemannResearch.RH.QCRTZeroGrowth
import RiemannResearch.RH.QCRTProjectedMellin
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A positive-logarithmic-variation criterion for the actual canonical CRT lifts

Source: user-provided `CanonicalPrimePowerUpdatesResearch20261107(1).md`,
Section 7. This conditional research reduction uses the actual
`QCRTZeroGrowth.lcmLift` and its existing Mellin zero obstruction. The
sublogarithmic positive-variation estimate remains an explicit open
canonical-specific hypothesis; this module does not establish RH outright.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QCRTPositiveLogVariation
open ZetaTwoProbability QCRTProjectedMellin QCRTZeroGrowth

/-- Complete canonical energy, with the repository's offset LCM indexing. -/
def canonicalEnergy (M : ℕ) : ℝ := ‖lcmLift M‖ ^ 2

/-- Positive variation of the logarithm of one plus complete canonical energy. -/
def canonicalLogVariation (M : ℕ) : ℝ :=
  Real.positiveVariation (fun n => Real.log (1 + canonicalEnergy n)) M

/-- Conditional research reduction. Open obligation: prove that the actual
canonical positive-logarithmic variation is `o (log (M + 2))`. -/
theorem riemannHypothesis_of_positive_log_variation
    (hvariation : Tendsto
      (fun M => canonicalLogVariation M / Real.log ((M + 2 : ℕ) : ℝ))
      atTop (𝓝 0)) : RiemannHypothesis := by
  have hsub : Tendsto
      (fun M => Real.log (1 + ‖lcmLift M‖ ^ 2) /
        Real.log ((M + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
    apply Real.log_ratio_tendsto_zero_of_positiveVariation
      (fun M : ℕ => ((M + 2 : ℕ) : ℝ)) (fun M => ‖lcmLift M‖ ^ 2)
      cutoff_tendsto_atTop (fun M => sq_nonneg _)
    simpa only [canonicalLogVariation, canonicalEnergy] using hvariation
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hZ := zetaTwo_pos
  have hA := escapeFactor_pos s
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have ha : 0 < 2 * s.re - 1 := by linarith
  apply RiemannResearch.Analysis.SubpolynomialWindow.no_positive_power_floor
    (fun M : ℕ => ((M + 2 : ℕ) : ℝ)) (fun M => ‖lcmLift M‖ ^ 2)
    1 ((2 * s.re - 1) / (4 * (escapeFactor s) ^ 2 * zetaTwo * ‖s‖ ^ 2))
    (2 * s.re - 1) cutoff_tendsto_atTop (fun M => sq_nonneg _)
    le_rfl (by positivity) ha hsub
  filter_upwards [canonical_leakage_power_floor s hs hslt hz] with M hM
  exact hM.trans ((lcmLeakage_le_norm_sq M).trans (by linarith))

end RiemannResearch.RH.QCRTPositiveLogVariation
