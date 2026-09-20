import RiemannResearch.Probability.DeterminantalWindowGenerating
import RiemannResearch.RH.IntegerDPPExistence

/-!
# Arithmetic finite-window generating functions

The expectation formulas are for the constructed integerLaw and limitingLaw.
All positivity inputs are discharged by the actual arithmetic orthogonal
projections. Source: the user-provided DPP/Fredholm construction.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Classical
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.Analysis.ProjectionDPP
open RiemannResearch.Probability.DPP

theorem integerLaw_window_generating (n m : ℕ) (e : Fin m ↪ ℕ) (z : Fin m → ℝ) :
    (∫ x, ∏ i : Fin m, if x (e i) = true then z i else 1 ∂integerLaw n) =
      (Matrix.diagonal z * Matrix.of (fun i j => integerKernel n (e i) (e j)) +
        (1 - Matrix.of (fun i j => integerKernel n (e i) (e j)))).det := by
  have h := (integerLaw_isDPP n).window_generating e
    (fun S => exactWeight_nonneg _
      (principal_posSemidef (finiteSpace n) countingBasis e)
      (integerKernel_principal_complement_posSemidef n m e) S) z
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with x
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hx : x (e i) = true <;> simp [hx]

theorem limitingLaw_window_generating (m : ℕ) (e : Fin m ↪ ℕ) (z : Fin m → ℝ) :
    (∫ x, ∏ i : Fin m, if x (e i) = true then z i else 1 ∂limitingLaw) =
      (Matrix.diagonal z * Matrix.of (fun i j => limitingKernel (e i) (e j)) +
        (1 - Matrix.of (fun i j => limitingKernel (e i) (e j)))).det := by
  have h := limitingLaw_isDPP.window_generating e
    (fun S => exactWeight_nonneg _
      (principal_posSemidef closedSpace countingBasis e)
      (limitingKernel_principal_complement_posSemidef m e) S) z
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with x
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hx : x (e i) = true <;> simp [hx]

theorem integerLaw_window_count_generating (n m : ℕ) (e : Fin m ↪ ℕ) (z : ℝ) :
    (∫ x, ∏ i : Fin m, if x (e i) = true then z else 1 ∂integerLaw n) =
      (1 + (z - 1) • Matrix.of (fun i j => integerKernel n (e i) (e j))).det := by
  have h := (integerLaw_isDPP n).window_count_generating e
    (fun S => exactWeight_nonneg _
      (principal_posSemidef (finiteSpace n) countingBasis e)
      (integerKernel_principal_complement_posSemidef n m e) S) z
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with x
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hx : x (e i) = true <;> simp [hx]

theorem limitingLaw_window_count_generating (m : ℕ) (e : Fin m ↪ ℕ) (z : ℝ) :
    (∫ x, ∏ i : Fin m, if x (e i) = true then z else 1 ∂limitingLaw) =
      (1 + (z - 1) • Matrix.of (fun i j => limitingKernel (e i) (e j))).det := by
  have h := limitingLaw_isDPP.window_count_generating e
    (fun S => exactWeight_nonneg _
      (principal_posSemidef closedSpace countingBasis e)
      (limitingKernel_principal_complement_posSemidef m e) S) z
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with x
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hx : x (e i) = true <;> simp [hx]

end RiemannResearch.RH.Pareto.IntegerDPP
