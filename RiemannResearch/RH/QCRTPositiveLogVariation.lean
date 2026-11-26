/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PositiveLogVariation
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import RiemannResearch.RH.QCRTZeroGrowth
import RiemannResearch.RH.QCRTFiniteCollocation
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


/-- Every actual canonical squared norm is positive. This follows from its
exact visible-target energy, without a growth assumption. -/
theorem canonicalEnergy_pos (M : ℕ) : 0 < canonicalEnergy M := by
  have hL : (2 : ℝ) ≤ (lcmStage M : ℝ) := by
    exact_mod_cast lcmStage_two_le M
  have hden : 0 < (lcmStage M : ℝ) ^ 2 := by positivity
  have hfrac : 1 / (lcmStage M : ℝ) ^ 2 < 1 := by
    apply (div_lt_one hden).2
    nlinarith
  have he := QCRTFiniteCollocation.canonical_norm (lcmStage M) (lcmStage_two_le M)
  change canonicalEnergy M = 1 - 1 / (lcmStage M : ℝ) ^ 2 + lcmLeakage M at he
  rw [he]
  linarith [lcmLeakage_nonneg M]

/-- The actual cumulative positive relative increment budget. -/
def canonicalRelativeVariation (M : ℕ) : ℝ :=
  Real.positiveRelativeVariation canonicalEnergy M

/-- The stronger relative-increment hypothesis implies the existing actual
positive-logarithmic-variation RH criterion. Its arithmetic estimate is open. -/
theorem riemannHypothesis_of_positive_relative_variation
    (hrelative : Tendsto
      (fun M => canonicalRelativeVariation M / Real.log ((M + 2 : ℕ) : ℝ))
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_positive_log_variation
  change Tendsto (fun M =>
    Real.positiveVariation (fun n => Real.log (1 + canonicalEnergy n)) M /
      Real.log ((M + 2 : ℕ) : ℝ)) atTop (𝓝 0)
  exact Real.positiveVariation_ratio_tendsto_zero_of_relative
    (fun M : ℕ => ((M + 2 : ℕ) : ℝ)) canonicalEnergy cutoff_tendsto_atTop
    canonicalEnergy_pos hrelative


/-- A zero forces growth of the upward variation even if only the selected
cutoffs are observed. The logarithmic factor in the energy floor contributes
an additive log-log term. -/
theorem sampled_logVariation_floor (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hslt : s.re < 1) (hz : riemannZeta s = 0) :
    ∃ b : ℝ, ∀ᶠ j : ℕ in atTop,
      (2 * s.re - 1) * Real.log ((M j + 2 : ℕ) : ℝ) +
        Real.log (Real.log ((M j + 2 : ℕ) : ℝ)) + b ≤
      Real.positiveVariation (fun i => Real.log (1 + canonicalEnergy (M i))) j := by
  obtain ⟨c, hc, hfloor⟩ := canonical_norm_sq_log_power_floor s hs hslt hz
  refine ⟨Real.log c - Real.log (1 + canonicalEnergy (M 0)), ?_⟩
  filter_upwards [hM.eventually hfloor] with j hj
  let X : ℝ := ((M j + 2 : ℕ) : ℝ)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast (show 1 < M j + 2 by omega)
  have hXp : 0 < X := zero_lt_one.trans hX
  have hL := Real.log_pos hX
  have hp := Real.rpow_pos_of_pos hXp (2 * s.re - 1)
  have he : c * X ^ (2 * s.re - 1) * Real.log X ≤ 1 + canonicalEnergy (M j) :=
    hj.trans (by unfold canonicalEnergy; linarith)
  have hlog := Real.log_le_log (mul_pos (mul_pos hc hp) hL) he
  rw [Real.log_mul (mul_pos hc hp).ne' hL.ne', Real.log_mul hc.ne' hp.ne',
    Real.log_rpow hXp] at hlog
  have hv := Real.le_initial_add_positiveVariation
    (fun i => Real.log (1 + canonicalEnergy (M i))) j
  change (2 * s.re - 1) * Real.log X + Real.log (Real.log X) +
    (Real.log c - Real.log (1 + canonicalEnergy (M 0))) ≤ _
  linarith only [hlog, hv]

/-- Only cofinally small positive variation along one unbounded schedule of
actual cutoffs is needed. Positive variations inside skipped blocks are free. -/
theorem riemannHypothesis_of_cofinal_sampled_logVariation (M : ℕ → ℕ)
    (hM : Tendsto M atTop atTop)
    (hsmall : ∀ a : ℝ, 0 < a → ∀ N : ℕ, ∃ j ≥ N,
      Real.positiveVariation (fun i => Real.log (1 + canonicalEnergy (M i))) j <
        a * Real.log ((M j + 2 : ℕ) : ℝ)) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  obtain ⟨b, hb⟩ := sampled_logVariation_floor M hM s hs hslt hz
  have hlog : Tendsto (fun j => Real.log (Real.log ((M j + 2 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (cutoff_tendsto_atTop.comp hM))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hb.and (hlog.eventually (eventually_ge_atTop (-b))))
  obtain ⟨j, hj, hsmallj⟩ := hsmall (2 * s.re - 1) (by linarith) N
  obtain ⟨hlo, hconst⟩ := hN j hj
  linarith only [hlo, hconst, hsmallj]

end RiemannResearch.RH.QCRTPositiveLogVariation
