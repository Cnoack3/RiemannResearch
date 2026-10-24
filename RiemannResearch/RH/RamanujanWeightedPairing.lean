import RiemannResearch.Analysis.WeightedObservationPairing
import RiemannResearch.RH.RamanujanAdmissibleWeights
import Mathlib.Tactic.Abel

/-!
# Complete mixed Ramanujan coefficient-defect laws

Source: sixth transfer program, 24 October 2026. The pairings below retain
every signed product of the two actual conductor-defect arrays. The exact
difference and interpolation identities precede their sharp energy bounds.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanWeightedPairing
open Pareto ZetaTwoHilbert RamanujanWeightedDefect RamanujanAdmissibleWeights
open RiemannResearch.Analysis.WeightedCoordinateEnergy
open RiemannResearch.Analysis.WeightedObservationPairing

def paretoCrossDefect (w : ℕ → ℝ) (n m : ℕ) : ℝ :=
  pairing w paretoCoordinates (hilbertOne - CoefficientStabilization.projection n)
    (hilbertOne - CoefficientStabilization.projection m)

def qCrossDefect (w : ℕ → ℝ) (n m : ℕ) : ℝ :=
  pairing w qCoordinates (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)
    (qOne - QRamanujanCanonicalOptimizer.packetCandidate m)

theorem paretoCrossDefect_series (w : ℕ → ℝ) (n m : ℕ) :
    paretoCrossDefect w n m = ∑' j, w j *
      (RamanujanCanonicalOptimizer.packetMultipleCoefficient n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) *
      (RamanujanCanonicalOptimizer.packetMultipleCoefficient m (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) := by
  unfold paretoCrossDefect pairing
  apply tsum_congr
  intro j
  rw [pareto_coordinate_residual, pareto_coordinate_residual]
  ring

theorem qCrossDefect_series (w : ℕ → ℝ) (n m : ℕ) :
    qCrossDefect w n m = ∑' j, w j *
      (QRamanujanCanonicalOptimizer.packetCoordinate n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) *
      (QRamanujanCanonicalOptimizer.packetCoordinate m (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) := by
  unfold qCrossDefect pairing
  apply tsum_congr
  intro j
  rw [q_coordinate_residual, q_coordinate_residual]
  ring

theorem pareto_difference_exact (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2)) (n m : ℕ) :
    observationEnergy w paretoCoordinates
      (CoefficientStabilization.projection m - CoefficientStabilization.projection n) =
      paretoDefectWith w n + paretoDefectWith w m - 2 * paretoCrossDefect w n m := by
  have h := energy_sub_exact w paretoCoordinates hw hs
    (hilbertOne - CoefficientStabilization.projection n)
    (hilbertOne - CoefficientStabilization.projection m)
  have he : (hilbertOne - CoefficientStabilization.projection n) -
      (hilbertOne - CoefficientStabilization.projection m) =
        CoefficientStabilization.projection m - CoefficientStabilization.projection n := by abel
  simpa only [he, paretoDefectWith, paretoCrossDefect] using h

theorem q_difference_exact (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2)) (n m : ℕ) :
    observationEnergy w qCoordinates
      (QRamanujanCanonicalOptimizer.packetCandidate m - QRamanujanCanonicalOptimizer.packetCandidate n) =
      qDefectWith w n + qDefectWith w m - 2 * qCrossDefect w n m := by
  have h := energy_sub_exact w qCoordinates hw hs
    (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)
    (qOne - QRamanujanCanonicalOptimizer.packetCandidate m)
  have he : (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) -
      (qOne - QRamanujanCanonicalOptimizer.packetCandidate m) =
        QRamanujanCanonicalOptimizer.packetCandidate m - QRamanujanCanonicalOptimizer.packetCandidate n := by abel
  simpa only [he, qDefectWith, qCrossDefect] using h

theorem pareto_cross_defect_sq_le (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2)) (n m : ℕ) :
    (paretoCrossDefect w n m) ^ 2 ≤ paretoDefectWith w n * paretoDefectWith w m :=
  pairing_sq_le w paretoCoordinates hw hs _ _

theorem q_cross_defect_sq_le (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2)) (n m : ℕ) :
    (qCrossDefect w n m) ^ 2 ≤ qDefectWith w n * qDefectWith w m :=
  pairing_sq_le w qCoordinates hw hs _ _

theorem pareto_interpolated_defect_exact (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2)) (n m : ℕ) (t : ℝ) :
    observationEnergy w paretoCoordinates
      ((1 - t) • (hilbertOne - CoefficientStabilization.projection n) +
        t • (hilbertOne - CoefficientStabilization.projection m)) =
      (1 - t) * paretoDefectWith w n + t * paretoDefectWith w m -
        t * (1 - t) * (paretoDefectWith w n + paretoDefectWith w m -
          2 * paretoCrossDefect w n m) := by
  rw [energy_affine_exact w paretoCoordinates hw hs,
    energy_sub_exact w paretoCoordinates hw hs
      (hilbertOne - CoefficientStabilization.projection n)
      (hilbertOne - CoefficientStabilization.projection m)] <;> rfl

theorem q_interpolated_defect_exact (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2)) (n m : ℕ) (t : ℝ) :
    observationEnergy w qCoordinates
      ((1 - t) • (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) +
        t • (qOne - QRamanujanCanonicalOptimizer.packetCandidate m)) =
      (1 - t) * qDefectWith w n + t * qDefectWith w m -
        t * (1 - t) * (qDefectWith w n + qDefectWith w m - 2 * qCrossDefect w n m) := by
  rw [energy_affine_exact w qCoordinates hw hs, energy_sub_exact w qCoordinates hw hs
    (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)
    (qOne - QRamanujanCanonicalOptimizer.packetCandidate m)] <;> rfl

end RiemannResearch.RH.RamanujanWeightedPairing
