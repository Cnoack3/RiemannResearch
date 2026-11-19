/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualSmallGapProportion
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Inverse-logarithmic abundance of actual small consecutive gaps

When the deleted endpoint fraction is at most C/(log T)^p, a sparse-pair
estimate can rule out such a subsequence using a fixed Fourier objective
M>1. This is the precise filter-theoretic consequence for the chronological
finite-cutoff gap fraction. The analytic estimate remains an explicit input.
-/

noncomputable section

open Filter
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

def logarithmicallyScaledGapFraction (gapLimit p T : ℝ) : ℝ :=
  (Real.log T)^p * smallGapFraction gapLimit T

/-- A bounded rescaled gap fraction forces the separated-pair objective down
to one, with an error tending to zero on each fixed cap. -/
def scaledSeparatedPairEstimate (scale : ℝ → ℝ) (gapLimit M : ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
    ∀ᶠ T in atTop, scale T * smallGapFraction gapLimit T ≤ C →
      M ≤ 1 + error T

theorem scaledGapFraction_tendsto_atTop {scale : ℝ → ℝ} {gapLimit M : ℝ}
    (hM : 1 < M) (hs : scaledSeparatedPairEstimate scale gapLimit M) :
    Tendsto (fun T => scale T * smallGapFraction gapLimit T) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro B
  have hc : 0 < max 1 B := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨error, he, hpair⟩ := hs _ hc
  have hε : 0 < M-1 := sub_pos.mpr hM
  have hsmall := Metric.tendsto_nhds.mp he (M-1) hε
  filter_upwards [hpair, hsmall] with T ht hdist
  by_contra! hneg
  have hbound := ht (hneg.le.trans (le_max_right _ _))
  rw [Real.dist_eq, sub_zero] at hdist
  have her := (abs_lt.mp hdist).2
  linarith

/-- Every fixed logarithmic rarity cap admits a vanishing separated-pair
error on the heights where that cap holds. -/
def sparseSeparatedPairEstimate (gapLimit p M : ℝ) : Prop :=
  scaledSeparatedPairEstimate (fun T => (Real.log T)^p) gapLimit M

theorem scaledGapFraction_tendsto_atTop_of_sparsePairEstimate
    {gapLimit p M : ℝ} (hM : 1 < M) (hs : sparseSeparatedPairEstimate gapLimit p M) :
    Tendsto (logarithmicallyScaledGapFraction gapLimit p) atTop atTop :=
  scaledGapFraction_tendsto_atTop hM hs

/-- Height-power rarity is the form used with fixed-strip density estimates
at Fourier supports above 2/3. -/
theorem polynomialGapFraction_tendsto_atTop_of_sparsePairEstimate
    {gapLimit p M : ℝ} (hM : 1 < M)
    (hs : scaledSeparatedPairEstimate (fun T => T^p) gapLimit M) :
    Tendsto (fun T : ℝ => T^p * smallGapFraction gapLimit T) atTop atTop :=
  scaledGapFraction_tendsto_atTop hM hs

end RiemannResearch.Analysis.ActualZeroOrdinate
