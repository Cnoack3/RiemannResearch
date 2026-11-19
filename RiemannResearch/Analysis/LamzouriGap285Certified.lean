/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285FiniteSigns
import RiemannResearch.Analysis.LamzouriGap285TraceCheck

namespace RiemannResearch.Analysis.LamzouriGapKernel285
open ActualZeroOrdinate LamzouriSmallGapCriterion

/-- The degree-285 integer witness gives a positive lower proportion of
adjacent gaps at most 0.784782678 times the mean spacing. -/
theorem smallGapProportion_degree285 [LamzouriCompactDeletion2026] :
    0 < smallGapProportion (392391339 / 500000000) :=
  smallGapProportion_of_degree285_transport trace_fourier

end RiemannResearch.Analysis.LamzouriGapKernel285
