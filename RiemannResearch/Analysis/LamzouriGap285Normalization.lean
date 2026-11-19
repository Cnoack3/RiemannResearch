/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriActualGap285
namespace RiemannResearch.Analysis.LamzouriGapKernel285
open GapKernelPolynomial GapKernelObjective
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem ratValue_zero (p : List ℤ) : ratValue p 0 = (p.headD 0 : ℚ) := by
  cases p <;> simp [ratValue]

/-- Strict positivity of the exact degree-285 Fourier normalization. -/
theorem unit_positive : 0 < ratValue fourierPolynomial 0 := by
  rw [ratValue_zero]
  exact_mod_cast (show (0 : ℤ) < fourierPolynomial.headD 0 by decide +kernel)

end RiemannResearch.Analysis.LamzouriGapKernel285
