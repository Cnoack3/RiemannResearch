/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryWindowVarianceCriterion
import RiemannResearch.Analysis.MontgomeryCentralPeak
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # The central Fourier contribution to fixed-width variance

The Fourier transform of the physical count overlap at width `R` is the
sinc-square test. The checked BGSTB central limit for a continuous test
cancels the squared finite-height mean at this particular test.
-/

noncomputable section

open Filter
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open MontgomeryFormFactor MontgomeryHorizontalBessel

/-- The central peak tested at the Fourier transform of the width-R triangle
accounts for the asymptotic square of the mean. -/
theorem raw_central_window_test_sub_mean_sq_tendsto_zero
    (h : BGSTBPositiveCutoffEstimate) (R : ℝ) :
    Tendsto (fun T : ℝ =>
      (∫ α in (-centralFourierRadius T)..centralFourierRadius T,
        (R ^ 2 * Real.sinc (Real.pi * R * α) ^ 2) * formFactor T α) -
        unfoldedWindowMean T R ^ 2) atTop (𝓝 0) := by
  let K : ℝ → ℝ := fun α => R ^ 2 * Real.sinc (Real.pi * R * α) ^ 2
  have hc : Continuous K := continuous_const.mul
    ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2)
  have hlim := (raw_central_test_tendsto_value h hc).sub ((unfoldedWindowMean_tendsto R).pow 2)
  simpa [K] using hlim

end RiemannResearch.Analysis.MontgomeryPositiveGap
