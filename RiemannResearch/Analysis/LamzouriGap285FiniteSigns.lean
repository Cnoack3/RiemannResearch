/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285PhysicalSignCheck
import RiemannResearch.Analysis.LamzouriGap285FourierRay
import RiemannResearch.Analysis.LamzouriGap285ObjectiveData

/-! # Degree-285 compact deletion with only the Fourier identity outstanding -/

namespace RiemannResearch.Analysis.LamzouriGapKernel285
open ActualZeroOrdinate GapKernelPolynomial GapKernelFourierRecurrence LamzouriSmallGapCriterion

theorem smallGapProportion_of_degree285_transport [LamzouriCompactDeletion2026]
    (h : transport physicalData = scale (2 ^ physicalData.length) frequencyData) :
    0 < smallGapProportion (392391339 / 500000000) :=
  smallGapProportion_of_polynomialCertificate physicalData frequencyData
    ⟨objective_data_checks.1, physicalData_positive, frequencyData_negative, h,
      objective_data_checks.2.1, objective_data_checks.2.2⟩

end RiemannResearch.Analysis.LamzouriGapKernel285
