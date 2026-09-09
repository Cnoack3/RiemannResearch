import RiemannResearch.RH.ParetoGibbsHilbert
import RiemannResearch.RH.ParetoGeometricTransform
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The full geometric transform and its actual adjoint: proof obligation

Source: Section 2 of the contracting-evolution research report.
The actual full-H Gibbs operator is proved elsewhere. This proposition asks
for its specific conditional-geometric L2 factorization, including agreement
with the scalar series and the integral adjoint formula. It is not an axiom
or a claimed theorem, and no proved Gibbs result depends on it.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section
open MeasureTheory

def geometricLatentMeasure : Measure ℝ := volume.restrict (Set.Ioo 0 1)

abbrev GeometricLatentL2 := Lp ℝ 2 geometricLatentMeasure

/-- A concrete realization on the full Hilbert space, rather than an
arbitrary factorization with no connection to the actual geometric series. -/
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
