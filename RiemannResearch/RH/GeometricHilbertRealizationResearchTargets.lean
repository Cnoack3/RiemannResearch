import RiemannResearch.RH.ParetoGibbsHilbert
import RiemannResearch.RH.ParetoGeometricTransform
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The full geometric transform and its actual adjoint: proved specification

Source: Section 2 of the contracting-evolution research report.
This proposition specifies the actual conditional-geometric L2 factorization
of the full Hilbert-space Gibbs operator, including agreement with the scalar
series and the integral adjoint formula. Its unconditional provider is
`geometricHilbertRealizationTarget_proved` in `GeometricHilbertRealizationProof`.
The proposition definition is not an axiom.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section
open MeasureTheory

def geometricLatentMeasure : Measure ℝ := volume.restrict (Set.Ioo 0 1)

abbrev GeometricLatentL2 := Lp ℝ 2 geometricLatentMeasure

/-- Concrete full-Hilbert-space realization of the actual geometric series,
supplied by `geometricHilbertRealizationTarget_proved` in
`GeometricHilbertRealizationProof`. -/
def GeometricHilbertRealizationTarget : Prop :=
  ∃ T : ThresholdHilbert →L[ℝ] GeometricLatentL2,
    ‖T‖ ≤ 1 ∧
    (∀ f : ThresholdHilbert, (∃ C : ℝ, ∀ n, |hilbertGibbsPhysical f n| ≤ C) →
      ∀ᵐ t ∂geometricLatentMeasure,
        T f t = geometricTransform (hilbertGibbsPhysical f) t) ∧
    (∀ g : GeometricLatentL2, ∀ n : ℕ,
      Integrable (fun t : ℝ => geometricProbability n t * g t) geometricLatentMeasure ∧
      hilbertGibbsPhysical ((ContinuousLinearMap.adjoint T) g) n =
        (∫ t : ℝ, geometricProbability n t * g t ∂geometricLatentMeasure) /
          paretoWeight n) ∧
    (ContinuousLinearMap.adjoint T).comp T = hilbertGibbsContinuous

end
end RiemannResearch.RH.Pareto
