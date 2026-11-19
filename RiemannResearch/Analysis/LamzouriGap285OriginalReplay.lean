/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.LamzouriGap285Certified
import RiemannResearch.Analysis.LamzouriGap285SourceVerification

namespace RiemannResearch.Analysis.LamzouriGapKernel285

/-- All six replay fields for the arrays constructed from the original
Laguerre coefficients, with their original common integer scale. -/
instance verifiedReplay : Replay where
  unit_pos := by rw [frequencyData_eq]; exact objective_data_checks.1
  input_pos := by rw [physicalData_eq]; exact physicalData_positive
  output_neg := by rw [frequencyData_eq]; exact frequencyData_negative
  coefficients := by rw [physicalData_eq, frequencyData_eq]; exact trace_fourier
  primitive_nonneg := by rw [physicalData_eq]; exact objective_data_checks.2.1
  scalar := by rw [physicalData_eq, frequencyData_eq]; exact objective_data_checks.2.2

end RiemannResearch.Analysis.LamzouriGapKernel285
