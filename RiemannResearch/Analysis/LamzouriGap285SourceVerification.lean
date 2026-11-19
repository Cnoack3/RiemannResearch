/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285CoefficientBlock0
import RiemannResearch.Analysis.LamzouriGap285CoefficientBlock1
import RiemannResearch.Analysis.LamzouriGap285CoefficientBlock2
import RiemannResearch.Analysis.LamzouriGap285CoefficientBlock3
import RiemannResearch.Analysis.LamzouriGap285CoefficientBlock4
import RiemannResearch.Analysis.LamzouriGap285CoefficientBlock5
import RiemannResearch.Analysis.LamzouriGap285CoefficientBlock6
import RiemannResearch.Analysis.LamzouriGap285CoefficientBlock7

namespace RiemannResearch.Analysis.LamzouriGapKernel285
open CoefficientTable

theorem physicalData_eq : inputPolynomial = physicalData :=
  p_source.trans (assemble false block0.1 block1.1 block2.1 block3.1 block4.1 block5.1 block6.1 block7.1)

theorem frequencyData_eq : fourierPolynomial = frequencyData :=
  q_source.trans (assemble true block0.2 block1.2 block2.2 block3.2 block4.2 block5.2 block6.2 block7.2)

end RiemannResearch.Analysis.LamzouriGapKernel285
