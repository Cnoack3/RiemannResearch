/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelSumOfSquares
import RiemannResearch.Analysis.LamzouriGap285DataCache
import RiemannResearch.Analysis.LamzouriGap285FourierSquares

namespace RiemannResearch.Analysis.LamzouriGapKernel285
open GapKernelPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shiftedFourierData : List ℤ := eval% scale (-1) (inputScale 25 (shift 78 (clearScale 25 frequencyData)))

theorem fourierSquareCheck :
    checkRay (squareRemainder (2 ^ 480) shiftedFourierData Squares.Fourier.even Squares.Fourier.odd) = true := by
  decide +kernel

theorem fourierData_positive (x : ℝ) (hx : 0 ≤ x) : 0 < value shiftedFourierData x :=
  positive_of_squareRemainder (by decide : 0 < (2 : ℤ) ^ 480) fourierSquareCheck x hx

end RiemannResearch.Analysis.LamzouriGapKernel285
