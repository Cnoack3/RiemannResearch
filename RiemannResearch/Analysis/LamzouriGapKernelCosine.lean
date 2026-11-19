/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGapKernelFourierPolynomial
import RiemannResearch.Analysis.LamzouriGapKernelSigns
import RiemannResearch.Analysis.GapKernelFourierScaling

noncomputable section
open MeasureTheory Real
namespace RiemannResearch.Analysis.LamzouriGapKernel
open GapKernelFourierGaussian GapKernelPolynomial

/-- The Fourier-side polynomial that was checked for strict negativity is
the actual cosine transform of the explicitly normalized input polynomial. -/
theorem normalized_cosineTransform {s : ℝ} (hs : 0 < s) (u : ℝ) :
    (∫ x : ℝ, normalizedTest inputPolynomial fourierPolynomial s x *
      Real.cos (2 * Real.pi * x * u)) = fourierModel s fourierPolynomial u :=
  normalized_fourier_cosine hs fourierPolynomial_zero_pos fourierPolynomial_transport u

end RiemannResearch.Analysis.LamzouriGapKernel
