/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelPackedBernstein
import RiemannResearch.Analysis.LamzouriGap285FourierSignCheck

namespace RiemannResearch.Analysis.LamzouriGapKernel285
open GapKernelPolynomial

set_option maxRecDepth 150000
set_option maxHeartbeats 0

private def cleared : List ℤ := eval% scale (-1) (clearScale 25 frequencyData)

private theorem cleared_eq : scale (-1) (clearScale 25 frequencyData) = cleared := by
  rfl

private theorem affine_eq : affineCoefficients 78 25 cleared = shiftedFourierData :=
  certifyAffine_sound _ _ _ _ (by decide +kernel)

theorem frequencyData_negative (y : ℝ) (hy : (78 / 25 : ℝ) ≤ y) :
    value frequencyData y < 0 := by
  have h := fourierData_positive (y - 78 / 25) (sub_nonneg.mpr hy)
  rw [← affine_eq, value_affineCoefficients, ← cleared_eq, value_scale,
    show (78 : ℤ) + (25 : ℤ) * (y - 78 / 25) = (25 : ℤ) * y by push_cast; ring,
    value_clearScale] at h
  have hp : 0 < (25 : ℝ) ^ frequencyData.length := by positivity
  push_cast at h
  by_contra! hn
  have hprod := mul_nonneg hp.le hn
  linarith only [h, hprod]

end RiemannResearch.Analysis.LamzouriGapKernel285
