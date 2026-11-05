/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QFixedHarmonic

/-! # A criterion using only finite stage projections and finite physical prefixes

Both the source residual and the correction use stage M. The cutoffs X are
cofinal, and for each such X arbitrarily large M may be used. No rate for M
as a function of X is assumed. In particular B = 0 and C = 1 give a single
threshold. Finite computations at finitely many X or M do not prove the bound.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QFixedHarmonic
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeSmoothedProjection QSquarefreeDisplacementRigidity

theorem vectorMinimum_continuous (X : ℕ) : Continuous (fun u : QHilbert => minimumHarmonicPrefixOf u X) := by
  simp only [minimumHarmonicPrefixOf, harmonicSideOf, ← qEvalCLM_apply]
  fun_prop

theorem movingCorrection_minimum_tendsto (X : ℕ) :
    Tendsto (fun M : ℕ => minimumHarmonicPrefixOf (movingCorrection M) X) atTop
      (𝓝 (minimumHarmonicPrefixOf correction X)) :=
  ((vectorMinimum_continuous X).tendsto correction).comp movingCorrection_tendsto

/-- Exact nested cofinality: each good physical cutoff admits unboundedly
many good finite projection stages. Both quantifiers have mathematical content. -/
theorem residual_zero_iff_cofinal_moving_harmonic (B C : ℝ) (hB : 0 ≤ B) (hC : 0 < C) :
    limitingResidual = 0 ↔ ∃ᶠ X : ℕ in atTop, ∃ᶠ M : ℕ in atTop,
      minimumHarmonicPrefixOf (movingCorrection M) X ≤ C * (Real.log (X : ℝ)) ^ B := by
  constructor
  · intro hr
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
    have hb : 0 < C * (Real.log (X : ℝ)) ^ B :=
      mul_pos hC (Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast (show 1 < X by omega))) B)
    have hm : minimumHarmonicPrefixOf correction X = 0 := by
      simp [minimumHarmonicPrefixOf, harmonicSideOf, correction, hr,
        show qSequence (0:QHilbert) = 0 from map_zero qSequenceLinear]
    have ht := movingCorrection_minimum_tendsto X
    rw [hm] at ht
    exact (ht.eventually (Iio_mem_nhds hb)).frequently.mono (fun _ h => le_of_lt h)
  · intro h
    apply residual_zero_iff_cofinal_correction_polylog.mpr
    refine ⟨B, C, hB, hC.le, h.mono ?_⟩
    intro X hX
    change minimumHarmonicPrefixOf correction X ≤ _
    by_contra hbad
    have hh := (movingCorrection_minimum_tendsto X).eventually (Ioi_mem_nhds (lt_of_not_ge hbad))
    obtain ⟨M, hM, hgt⟩ := (hX.and_eventually hh).exists
    exact (not_lt_of_ge hM) hgt

/-- A universal fixed threshold of one suffices on these two cofinal stages. -/
theorem residual_zero_iff_cofinal_moving_harmonic_one :
    limitingResidual = 0 ↔ ∃ᶠ X : ℕ in atTop, ∃ᶠ M : ℕ in atTop,
      minimumHarmonicPrefixOf (movingCorrection M) X ≤ 1 := by
  simpa using residual_zero_iff_cofinal_moving_harmonic 0 1 (by norm_num) (by norm_num)

end RiemannResearch.RH.QFixedHarmonic
