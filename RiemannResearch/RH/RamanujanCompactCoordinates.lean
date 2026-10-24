import RiemannResearch.Analysis.CompactObservationMap
import RiemannResearch.Analysis.NonnegativeErrorConvergence
import RiemannResearch.RH.RamanujanAdmissibleWeights
import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.RH.QTriangularDualDensity
import Lean.Elab.Tactic.Omega

/-!
# Compact, injective complete Ramanujan coefficient maps

Source: the compact weighted-observation construction applied to the actual
Pareto and Q conductor functionals. These are operators on the whole Hilbert
spaces, not just maps on canonical approximants. Every positive weighting with
a finite weighted squared operator-norm moment is permitted. The coefficient
error arrays are complete ℓ² vectors, with finite-rank uniform certificates.
The RH converses retain the explicit Open Baez--Duarte provider.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanCompactCoordinates
open Pareto ZetaTwoHilbert RamanujanWeightedDefect RamanujanAdmissibleWeights
open RiemannResearch.Analysis.CompactObservationMap
open RiemannResearch.Analysis.WeightedCoordinateEnergy
open RiemannResearch.Analysis.NonnegativeErrorConvergence

/-- All admissibly weighted Pareto conductor coefficients, as one ℓ² vector. -/
def paretoMap (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2)) :
    ThresholdHilbert →L[ℝ] CoordinateHilbert ℕ := coordinateMap w paretoCoordinates hw hs

/-- All admissibly weighted Q conductor coefficients, as one ℓ² vector. -/
def qMap (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2)) :
    QHilbert →L[ℝ] CoordinateHilbert ℕ := coordinateMap w qCoordinates hw hs

/-- Joint separation uses every conductor and the actual Möbius inversion. -/
theorem pareto_coordinates_separate (x : ThresholdHilbert)
    (h : ∀ j, paretoCoordinates j x = 0) : x = 0 := by
  apply eq_zero_of_mobius_coordinates_zero
  intro m hm
  have hi := h (m - 2)
  have he : m - 2 + 2 = m := by omega
  simpa only [paretoCoordinates, he, CoefficientStabilization.coefficientCLM,
    ContinuousLinearMap.neg_apply, neg_eq_zero] using hi

theorem q_coordinates_separate (x : QHilbert)
    (h : ∀ j, qCoordinates j x = 0) : x = 0 :=
  QTriangularCharge.q_eq_zero_of_all_coefficients_zero x h

/-- The observation map is compact and injective on the entire actual space. -/
theorem paretoMap_compact_injective (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2)) :
    IsCompactOperator (paretoMap w (fun j => (hw j).le) hs) ∧
      Function.Injective (paretoMap w (fun j => (hw j).le) hs) :=
  ⟨coordinateMap_isCompactOperator w paretoCoordinates (fun j => (hw j).le) hs,
    coordinateMap_injective w paretoCoordinates hw hs pareto_coordinates_separate⟩

theorem qMap_compact_injective (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2)) :
    IsCompactOperator (qMap w (fun j => (hw j).le) hs) ∧
      Function.Injective (qMap w (fun j => (hw j).le) hs) :=
  ⟨coordinateMap_isCompactOperator w qCoordinates (fun j => (hw j).le) hs,
    coordinateMap_injective w qCoordinates hw hs q_coordinates_separate⟩

/-- Positive-atom coefficients have target -μ, explaining the sign of this error. -/
theorem pareto_residual_coordinate (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2)) (n j : ℕ) :
    paretoMap w hw hs (hilbertOne - CoefficientStabilization.projection n) j =
      -Real.sqrt (w j) * (RamanujanCanonicalOptimizer.packetMultipleCoefficient n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) := by
  simp only [paretoMap, coordinateMap_apply, pareto_coordinate_residual, mul_neg, neg_mul]

theorem q_residual_coordinate (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2)) (n j : ℕ) :
    qMap w hw hs (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) j =
      -Real.sqrt (w j) * (QRamanujanCanonicalOptimizer.packetCoordinate n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) := by
  simp only [qMap, coordinateMap_apply, q_coordinate_residual, mul_neg, neg_mul]

/-- The exact complete defect is the squared ℓ² norm, without truncation. -/
theorem pareto_residual_norm_sq (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2)) (n : ℕ) :
    ‖paretoMap w hw hs (hilbertOne - CoefficientStabilization.projection n)‖ ^ 2 =
      paretoDefectWith w n :=
  coordinateMap_norm_sq w paretoCoordinates hw hs _

theorem q_residual_norm_sq (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2)) (n : ℕ) :
    ‖qMap w hw hs (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)‖ ^ 2 =
      qDefectWith w n :=
  coordinateMap_norm_sq w qCoordinates hw hs _

/-- Every finite conductor set has its exact omitted-energy remainder. -/
theorem pareto_finite_completion (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2)) (s : Finset ℕ) (n : ℕ) :
    paretoDefectWith w n = (∑ j ∈ s, w j *
      (RamanujanCanonicalOptimizer.packetMultipleCoefficient n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) ^ 2) +
      ‖paretoMap w hw hs (hilbertOne - CoefficientStabilization.projection n) -
        finiteMap w paretoCoordinates s (hilbertOne - CoefficientStabilization.projection n)‖ ^ 2 := by
  simpa only [paretoDefectWith, paretoMap, pareto_coordinate_residual, neg_sq] using
    finiteMap_error_completion w paretoCoordinates hw hs s
      (hilbertOne - CoefficientStabilization.projection n)

theorem q_finite_completion (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2)) (s : Finset ℕ) (n : ℕ) :
    qDefectWith w n = (∑ j ∈ s, w j *
      (QRamanujanCanonicalOptimizer.packetCoordinate n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) ^ 2) +
      ‖qMap w hw hs (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) -
        finiteMap w qCoordinates s (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)‖ ^ 2 := by
  simpa only [qDefectWith, qMap, q_coordinate_residual, neg_sq] using
    finiteMap_error_completion w qCoordinates hw hs s
      (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)

/-- A single finite observation set controls all Pareto optimization levels. -/
theorem pareto_uniform_finite_error (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖paretoCoordinates j‖ ^ 2)) (s : Finset ℕ) (n : ℕ) :
    ‖paretoMap w hw hs (hilbertOne - CoefficientStabilization.projection n) -
      finiteMap w paretoCoordinates s (hilbertOne - CoefficientStabilization.projection n)‖ ^ 2 ≤
        tailMass w paretoCoordinates s := by
  refine (finiteMap_error_sq_le w paretoCoordinates hw hs s _).trans ?_
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left (pareto_residual_bound n)
      (tailMass_nonneg w paretoCoordinates hw s))

theorem q_uniform_finite_error (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => w j * ‖qCoordinates j‖ ^ 2)) (s : Finset ℕ) (n : ℕ) :
    ‖qMap w hw hs (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) -
      finiteMap w qCoordinates s (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)‖ ^ 2 ≤
        tailMass w qCoordinates s := by
  refine (finiteMap_error_sq_le w qCoordinates hw hs s _).trans ?_
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left (q_residual_bound n)
      (tailMass_nonneg w qCoordinates hw s))

/-- RH is exactly strong ℓ² convergence of either complete weighted conductor
error vector, along every cofinal schedule and every admissible positive weighting. -/
theorem compact_coordinate_rh_equivalences
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (wP wQ : ℕ → ℝ) (hwP : ∀ j, 0 < wP j) (hwQ : ∀ j, 0 < wQ j)
    (hsP : Summable (fun j => wP j * ‖paretoCoordinates j‖ ^ 2))
    (hsQ : Summable (fun j => wQ j * ‖qCoordinates j‖ ^ 2))
    {α : Type*} {l : Filter α} [NeBot l] (N : α → ℕ) (hN : Tendsto N l atTop) :
    (Tendsto (fun i => paretoMap wP (fun j => (hwP j).le) hsP
        (hilbertOne - CoefficientStabilization.projection (N i))) l (𝓝 0) ↔
      RiemannHypothesis) ∧
    (Tendsto (fun i => qMap wQ (fun j => (hwQ j).le) hsQ
        (qOne - QRamanujanCanonicalOptimizer.packetCandidate (N i))) l (𝓝 0) ↔
      RiemannHypothesis) := by
  have h := admissible_weight_rh_equivalences hBaezDuarte wP wQ hwP hwQ hsP hsQ N hN
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero, norm_zero_iff_square]
    simpa only [pareto_residual_norm_sq] using h.1
  · rw [tendsto_zero_iff_norm_tendsto_zero, norm_zero_iff_square]
    simpa only [q_residual_norm_sq] using h.2

end RiemannResearch.RH.RamanujanCompactCoordinates
