import RiemannResearch.RH.PhaseCenteredAnalyticProviderProof
import RiemannResearch.RH.PairedMellinFromPhase

/-! Actual paired annihilators and their unconditional decomposition obstruction. -/

namespace RiemannResearch.RH.Pareto.CompressedMellin
noncomputable section

/-- The original paired-annihilator obligation, supplied by the actual analytic operator. -/
theorem actualPairedMellinProvider_proved : ActualPairedMellinProvider :=
  actualPairedMellinProvider_of_phase phaseCenteredAnalyticProvider_proved

/-- The constant vector cannot be exactly split between the separately closed seed spaces. -/
theorem actual_no_exact_decomposition_proved :
    ¬ ∃ f ∈ hilbertLegalClosure ({2} : Set ℕ),
      ∃ g ∈ hilbertLegalClosure ({3} : Set ℕ), hilbertOne = f + g :=
  actual_no_exact_decomposition actualPairedMellinProvider_proved

/-- Complete-space approximation forces reciprocal-error growth in both channels. -/
theorem actual_reciprocal_error_obstruction_proved :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
      ∀ f ∈ hilbertLegalClosure ({2} : Set ℕ),
      ∀ g ∈ hilbertLegalClosure ({3} : Set ℕ),
      ∀ ε : ℝ, 0 < ε → 2 * C * ε ≤ δ₀ →
      ‖hilbertOne - (f + g)‖ ≤ ε →
      1 / (4 * C * ε) ≤ ‖f‖ ∧ 1 / (4 * C * ε) ≤ ‖g‖ :=
  actual_reciprocal_error_obstruction actualPairedMellinProvider_proved

end
end RiemannResearch.RH.Pareto.CompressedMellin
