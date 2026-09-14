import RiemannResearch.RH.PhaseCenteredActualOperator
import RiemannResearch.RH.WeightedComplexPairingBound
import RiemannResearch.RH.ParetoCompressedMellinUniformBound

namespace RiemannResearch.RH.Pareto.CompressedMellin
noncomputable section

/-- Centering changes only phase, so it preserves every physical cell norm. -/
theorem phaseCenteredMellinCell_norm (t : ℝ) (n : ℕ) :
    ‖phaseCenteredMellinCell t n‖ = ‖compressedMellinCell t n‖ := by
  unfold phaseCenteredMellinCell
  rw [norm_mul, Complex.norm_exp]
  simp

/-- The actual centered cells retain the complete weighted square summability. -/
theorem phaseCenteredMellinCell_square_summable (t : ℝ) :
    Summable (fun n => paretoWeight n * ‖phaseCenteredMellinCell t n‖^2) := by
  simpa only [phaseCenteredMellinCell_norm] using compressedMellinCell_square_summable t

/-- Sharp real-to-complex operator estimate by the complete Riesz energy. -/
theorem actualPhaseCenteredOperator_norm_sq_le_energy (t : ℝ) :
    ‖actualPhaseCenteredOperator t‖^2 ≤ compressedMellinEnergy t := by
  have h := weighted_complex_operator_norm_sq_le
    (actualPhaseCenteredOperator t) (phaseCenteredMellinCell t)
    (phaseCenteredMellinCell_square_summable t)
    (fun f => actualPhaseCenteredOperator_eq_pairing t f)
  simpa only [phaseCenteredMellinCell_norm, compressedMellinEnergy] using h

/-- Exactly the uniform operator estimate requested in PhaseCenteredAnalyticProvider. -/
theorem actualPhaseCenteredOperator_norm_sq_le_seven_div (t : ℝ) (ht : 1 ≤ t) :
    ‖actualPhaseCenteredOperator t‖^2 ≤ 7 / t :=
  (actualPhaseCenteredOperator_norm_sq_le_energy t).trans
    (compressedMellinEnergy_le_seven_div t ht)

end
end RiemannResearch.RH.Pareto.CompressedMellin
