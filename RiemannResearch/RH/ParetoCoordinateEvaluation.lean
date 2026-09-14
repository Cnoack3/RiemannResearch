import RiemannResearch.RH.ParetoGibbsTailBasis

/-!
# Actual continuous positive-coordinate evaluations in the Pareto Hilbert space

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Section 4. Each physical evaluation is represented by the actual weighted
point vector, including its exact normalization.
-/
namespace RiemannResearch.RH.Pareto
noncomputable section

def physicalEvaluationCLM (n : ℕ) : ThresholdHilbert →L[ℝ] ℝ :=
  (paretoWeight n)⁻¹ • innerSL ℝ (paretoPointHilbert n)

@[simp] theorem physicalEvaluationCLM_apply (n : ℕ) (f : ThresholdHilbert) :
    physicalEvaluationCLM n f = hilbertSequence f (n + 1) := by
  change (paretoWeight n)⁻¹ * inner ℝ (paretoPointHilbert n) f = _
  rw [real_inner_comm, inner_paretoPoint, hilbertGibbsPhysical_eq]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (paretoWeight_pos n)), one_mul]


end
end RiemannResearch.RH.Pareto
