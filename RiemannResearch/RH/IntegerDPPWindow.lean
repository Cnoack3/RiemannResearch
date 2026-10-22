import RiemannResearch.Probability.DeterminantalWindow
import RiemannResearch.RH.IntegerDPPExistence

/-!
# Exact arithmetic DPP window probabilities

Source: the user-provided arithmetic DPP/Fredholm construction. Every window
formula below is for the previously constructed probability laws, and the
positive-contraction hypotheses are proved from the actual residue projections.
-/

noncomputable section
open MeasureTheory Matrix
open scoped Classical
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.Analysis.ProjectionDPP
open RiemannResearch.Probability.DPP

theorem integerLaw_finite_gap (n m : ℕ) (e : Fin m ↪ ℕ) :
    (integerLaw n).real {x | ∀ i, x (e i) = false} =
      (1 - Matrix.of (fun i j => integerKernel n (e i) (e j))).det := by
  have h := (integerLaw_isDPP n).finite_gap e
    (fun S => exactWeight_nonneg _
      (principal_posSemidef (finiteSpace n) countingBasis e)
      (integerKernel_principal_complement_posSemidef n m e) S)
  simpa using h

theorem limitingLaw_finite_gap (m : ℕ) (e : Fin m ↪ ℕ) :
    limitingLaw.real {x | ∀ i, x (e i) = false} =
      (1 - Matrix.of (fun i j => limitingKernel (e i) (e j))).det := by
  have h := limitingLaw_isDPP.finite_gap e
    (fun S => exactWeight_nonneg _
      (principal_posSemidef closedSpace countingBasis e)
      (limitingKernel_principal_complement_posSemidef m e) S)
  simpa using h

end RiemannResearch.RH.Pareto.IntegerDPP
