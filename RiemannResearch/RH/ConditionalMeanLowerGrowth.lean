/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ConditionalMeanNormalization
import RiemannResearch.RH.ConditionalMeanSubpolynomial
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import RiemannResearch.Analysis.LowerLogGrowth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Normalized Cesàro energy and lower logarithmic growth

Source: user-provided
`Conditional_IID_Pareto_Cesaro_Research_Agenda_2026-11-01.md`,
Sections 8 and 11.5. This formalizes the stated sufficient condition;
it does not construct a family meeting its arithmetic growth premise.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto

theorem riemannHypothesis_of_cofinally_small_conditionalMean_heads
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ)
    (hg : ∀ j, g j ∈ legalSeedSpan A)
    (hhead : ∀ j n, 0 < n → n ≤ Y j → g j n = 1)
    (hY : Tendsto Y atTop atTop)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ j in atTop,
      Real.log (1 + conditionalMeanSquare (g j)) / Real.log (Y j : ℝ) < ε) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hsadd : s + 1 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h
    linarith
  have hc : 0 < (2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2) := by
    apply div_pos (by linarith)
    exact mul_pos (by norm_num) (sq_pos_of_pos
      (norm_pos_iff.mpr (mul_ne_zero hs0 hsadd)))
  have hfloor : ∀ᶠ j : ℕ in atTop,
      ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) *
        (Y j : ℝ) ^ (2 * s.re - 1) ≤ conditionalMeanSquare (g j) + 1 := by
    filter_upwards [hY.eventually
      (exact_head_polynomial_obstruction_eventually A hA s hs hs1 hz)] with j hj
    exact (hj (g j) (hg j) (hhead j)).trans (le_add_of_nonneg_right zero_le_one)
  exact Analysis.SubpolynomialWindow.no_positive_power_floor_of_frequently_small_relativeLog
    (fun j => (Y j : ℝ)) (fun j => conditionalMeanSquare (g j)) 1
    ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) (2 * s.re - 1)
    (tendsto_natCast_atTop_atTop.comp hY) (fun j => conditionalMeanSquare_nonneg (g j))
    (by norm_num) hc (by linarith) hsmall hfloor


theorem normalized_exact_head_polynomial_obstruction_eventually
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∀ᶠ N : ℕ in atTop, ∀ g ∈ legalSeedSpan A, ∀ c : ℝ, c ≠ 0 →
      (∀ n, 0 < n → n ≤ N → g n = c) →
      ((2 * s.re - 1) / (12 * ‖s * (s + 1)‖ ^ 2)) *
        (N : ℝ) ^ (2 * s.re - 1) ≤ conditionalMeanSquare g / |c| ^ 2 := by
  filter_upwards [exact_head_polynomial_obstruction_eventually A hA s hs hs1 hz] with N hN
  intro g hg c hc hhead
  have hmem : (fun n => c⁻¹ * g n) ∈ legalSeedSpan A := by
    simpa only [Pi.smul_def, smul_eq_mul] using (legalSeedSpan A).smul_mem c⁻¹ hg
  have hhead' (n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
      c⁻¹ * g n = 1 := by rw [hhead n hn hnN, inv_mul_cancel₀ hc]
  simpa only [conditionalMeanSquare_normalize] using
    hN (fun n => c⁻¹ * g n) hmem hhead'

/-- No positive lower bound on the magnitudes of the head values is required. -/
theorem riemannHypothesis_of_cofinally_small_normalized_conditionalMean
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ) (c : ℕ → ℝ)
    (hg : ∀ j, g j ∈ legalSeedSpan A) (hc : ∀ j, c j ≠ 0)
    (hhead : ∀ j n, 0 < n → n ≤ Y j → g j n = c j)
    (hY : Tendsto Y atTop atTop)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ j in atTop,
      Real.log (1 + conditionalMeanSquare (g j) / |c j| ^ 2) /
        Real.log (Y j : ℝ) < ε) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinally_small_conditionalMean_heads A hA
    (fun j n => (c j)⁻¹ * g j n) Y
  · intro j
    simpa only [Pi.smul_def, smul_eq_mul] using
      (legalSeedSpan A).smul_mem (c j)⁻¹ (hg j)
  · intro j n hn hnY
    rw [hhead j n hn hnY, inv_mul_cancel₀ (hc j)]
  · exact hY
  · simpa only [conditionalMeanSquare_normalize] using hsmall

/-- The manuscript's normalized liminf-zero sufficient condition, with a
genuine extended lower limit and the actual Mathlib RH conclusion. -/
theorem riemannHypothesis_of_lowerLogGrowth_normalized_conditionalMean_zero
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (g : ℕ → ℕ → ℝ) (Y : ℕ → ℕ) (c : ℕ → ℝ)
    (hg : ∀ j, g j ∈ legalSeedSpan A) (hc : ∀ j, c j ≠ 0)
    (hhead : ∀ j n, 0 < n → n ≤ Y j → g j n = c j)
    (hY : Tendsto Y atTop atTop)
    (hlower : Analysis.SubpolynomialWindow.lowerLogGrowth
      (fun j => conditionalMeanSquare (g j) / |c j| ^ 2)
      (fun j => (Y j : ℝ)) = 0) : RiemannHypothesis :=
  riemannHypothesis_of_cofinally_small_normalized_conditionalMean A hA g Y c
    hg hc hhead hY
    ((Analysis.SubpolynomialWindow.lowerLogGrowth_eq_zero_iff _ _).mp hlower)

end RiemannResearch.RH.Pareto
