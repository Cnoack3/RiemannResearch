import RiemannResearch.RH.PhaseCenteredOperatorUniformBound
import RiemannResearch.RH.PhaseCenteredDerivativeBound

/-! The complete phase-centered analytic provider on the actual physical Hilbert space. -/

namespace RiemannResearch.RH.Pareto.CompressedMellin
noncomputable section

/-- All clauses of the original analytic specification, with its original constants. -/
theorem phaseCenteredAnalyticProvider_proved : PhaseCenteredAnalyticProvider := by
  refine ⟨actualPhaseCenteredOperator, actualPhaseCenteredOperator_eq_pairing,
    actualPhaseCenteredOperator_norm_sq_le_seven_div, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact actualPhaseCenteredOperator_one_norm t
  · intro t ht
    exact actualPhaseCenteredOperator_differentiableAt t (zero_lt_one.trans_le ht)
  · intro t ht
    rw [actualPhaseCenteredOperator_deriv t (zero_lt_one.trans_le ht)]
    exact actualPhaseCenteredDerivativeOperator_norm_bound t ht
  · intro b hb m hm f hf
    exact actualPhaseCenteredOperator_resonance b hb m hm hf

end
end RiemannResearch.RH.Pareto.CompressedMellin
