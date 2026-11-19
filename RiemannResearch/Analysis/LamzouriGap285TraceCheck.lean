/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285FourierBlock0
import RiemannResearch.Analysis.LamzouriGap285FourierBlock1
import RiemannResearch.Analysis.LamzouriGap285FourierBlock2
import RiemannResearch.Analysis.LamzouriGap285FourierBlock3
import RiemannResearch.Analysis.LamzouriGap285FourierBlock4
import RiemannResearch.Analysis.LamzouriGap285FourierBlock5
import RiemannResearch.Analysis.LamzouriGap285FourierBlock6
import RiemannResearch.Analysis.LamzouriGap285FourierBlock7

namespace RiemannResearch.Analysis.LamzouriGapKernel285
open FourierBlocks GapKernelFourierRecurrence GapKernelPolynomial

set_option maxRecDepth 120000
set_option maxHeartbeats 0

theorem trace_fourier : transport physicalData = scale (2 ^ physicalData.length) frequencyData := by
  have start : transport (inputAt (cut 0)) = checkpoint 0 := by decide +kernel
  have finish := checked7 (checked6 (checked5 (checked4 (checked3 (checked2 (checked1 (checked0 start)))))))
  have hi : inputAt (cut 8) = physicalData := by decide +kernel
  have ho : checkpoint 8 = scale (2 ^ physicalData.length) frequencyData := by decide +kernel
  change transport (inputAt (cut 8)) = checkpoint 8 at finish
  rwa [hi, ho] at finish

end RiemannResearch.Analysis.LamzouriGapKernel285
