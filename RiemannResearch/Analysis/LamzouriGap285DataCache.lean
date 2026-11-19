/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGapKernel285
import Mathlib.Tactic.Eval

/-! # Checked monomial coefficient arrays for the degree-285 gap witness

The elaborator produces the entries from the given Laguerre weights.
Definitional equality checks every entry of each array independently
of the computation that produced the proposed numerals.
-/

namespace RiemannResearch.Analysis.LamzouriGapKernel285

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def physicalData : List ℤ := eval% inputPolynomial
def frequencyData : List ℤ := eval% fourierPolynomial

end RiemannResearch.Analysis.LamzouriGapKernel285
