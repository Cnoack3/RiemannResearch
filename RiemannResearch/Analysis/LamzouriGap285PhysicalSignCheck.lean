/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelSumOfSquares
import RiemannResearch.Analysis.LamzouriGap285DataCache
import RiemannResearch.Analysis.LamzouriGap285PhysicalSquares

namespace RiemannResearch.Analysis.LamzouriGapKernel285
open GapKernelPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem physicalSquareCheck :
    checkRay (squareRemainder (2 ^ 480) physicalData Squares.Physical.even Squares.Physical.odd) = true := by
  decide +kernel

theorem physicalData_positive (x : ℝ) (hx : 0 ≤ x) : 0 < value physicalData x :=
  positive_of_squareRemainder (by decide : 0 < (2 : ℤ) ^ 480) physicalSquareCheck x hx

end RiemannResearch.Analysis.LamzouriGapKernel285
