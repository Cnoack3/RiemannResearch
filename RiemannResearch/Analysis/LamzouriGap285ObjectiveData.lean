/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriActualGap285
import RiemannResearch.Analysis.LamzouriGap285DataCache

/-! # Rational objective and Fourier recurrence for the degree-285 witness

The exact constants are the finite data in BoundCertificateReplays20261119.md. -/

namespace RiemannResearch.Analysis.LamzouriGapKernel285
open GapKernelPolynomial GapKernelObjective GapKernelFourierRecurrence

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def primitiveData : List ℤ := eval% primitiveFrom 0 physicalData

private theorem ratValue_zero (p : List ℤ) : ratValue p 0 = (p.headD 0 : ℚ) := by
  cases p <;> simp [ratValue]

theorem objective_data_checks :
    0 < ratValue frequencyData 0 ∧
    0 ≤ ratValue (primitiveFrom 0 physicalData) (radius ^ 2) ∧
    (177245385090551603 / 100000000000000000 : ℚ) * ratValue frequencyData 0 <
      (radius / cutoff) * ratValue physicalData 0 + (cutoff / radius) *
        (ratValue (primitiveFrom 0 physicalData) 0 -
          ratValue (primitiveFrom 0 physicalData) (radius ^ 2) / expLower (radius ^ 2) 32) := by
  have hprim : primitiveFrom 0 physicalData = primitiveData := by rfl
  rw [hprim, ratValue_zero frequencyData, ratValue_zero physicalData, ratValue_zero primitiveData]
  decide +kernel

end RiemannResearch.Analysis.LamzouriGapKernel285
