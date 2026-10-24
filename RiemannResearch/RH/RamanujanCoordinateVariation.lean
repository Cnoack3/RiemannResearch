import RiemannResearch.Analysis.ProjectionVariation
import RiemannResearch.RH.RamanujanCoordinateCapacityLimits
import RiemannResearch.RH.QRamanujanSaturationCriteria
import Mathlib.Tactic.Linarith

/-!
# Absolute variation of actual Pareto and Q Ramanujan coordinates

Source: fifth Ramanujan transfer program, 24 October 2026.
Each fixed signed multiple coordinate has finite absolute variation.
The sharp tail budget multiplies the remaining target energy by the
remaining capacity of its continuous coordinate representer. The Q result
uses the actual Q projections and the actual Q Riesz vector.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanCoordinateVariation
open Pareto ZetaTwoHilbert SquarefreeMobiusProjection
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionVariation

theorem pareto_coordinate_variation_tail_sq_le (N m : ℕ) (hm : 1 < m) :
    (∑' j, |Pareto.CoefficientStabilization.coefficient (j + N + 1) m - Pareto.CoefficientStabilization.coefficient (j + N) m|) ^ 2 ≤
      (RamanujanCoefficientConstraints.coordinateLimitCapacity m - RamanujanCoefficientConstraints.coordinateCapacity N m) *
        (Pareto.CoefficientStabilization.energy N - Pareto.CoefficientStabilization.limitEnergy) := by
  have h := variation_tail_sq_le Pareto.CoefficientStabilization.residueAtom id Function.surjective_id
    (RamanujanCoefficientConstraints.coordinateRiesz m) hilbertOne N
  have hg : walkError Pareto.CoefficientStabilization.residueAtom id (RamanujanCoefficientConstraints.coordinateRiesz m) N -
      limitingError Pareto.CoefficientStabilization.residueAtom (RamanujanCoefficientConstraints.coordinateRiesz m) =
        RamanujanCoefficientConstraints.coordinateLimitCapacity m - RamanujanCoefficientConstraints.coordinateCapacity N m := by
    have he := walkError_eq_limitingError_add Pareto.CoefficientStabilization.residueAtom id (RamanujanCoefficientConstraints.coordinateRiesz m) N
    have hc := RamanujanCoefficientConstraints.coordinateCapacity_limit_exact N m hm
    change RamanujanCoefficientConstraints.coordinateLimitCapacity m = RamanujanCoefficientConstraints.coordinateCapacity N m +
      ‖(dictionaryClosure Pareto.CoefficientStabilization.residueAtom).starProjection (RamanujanCoefficientConstraints.coordinateRiesz m) -
        (walkSpan Pareto.CoefficientStabilization.residueAtom id N).starProjection (RamanujanCoefficientConstraints.coordinateRiesz m)‖ ^ 2 at hc
    linarith
  rw [hg] at h
  simpa only [observation, RamanujanCoefficientConstraints.coordinateRiesz_inner, Pareto.CoefficientStabilization.coefficient, Pareto.CoefficientStabilization.projection,
    Pareto.CoefficientStabilization.finiteSpace, Pareto.CoefficientStabilization.energy, Pareto.CoefficientStabilization.limitEnergy] using h

def qCoordinateRiesz (m : ℕ) : QHilbert :=
  coordinateRiesz (qCoefficientCLM m)

def qCoordinateCapacity (n m : ℕ) : ℝ :=
  ‖(QFullResidueProjection.stage n).starProjection (qCoordinateRiesz m)‖ ^ 2

def qCoordinateLimitCapacity (m : ℕ) : ℝ :=
  ‖QFullResidueProjection.closure.starProjection (qCoordinateRiesz m)‖ ^ 2

theorem qCoordinateRiesz_inner (m : ℕ) (x : QHilbert) :
    inner ℝ (qCoordinateRiesz m) x = qCoefficientCLM m x :=
  InnerProductSpace.toDual_symm_apply

theorem qCoordinateCapacity_tendsto (m : ℕ) :
    Tendsto (fun n => qCoordinateCapacity n m) atTop (𝓝 (qCoordinateLimitCapacity m)) := by
  simpa only [qCoordinateCapacity, qCoordinateLimitCapacity, QFullResidueProjection.stage,
    QFullResidueProjection.closure, QFullResidueProjection.legalSpan, dictionaryClosure] using
    (walkProjection_tendsto (fun i : ℕ => qResidue (i + 2)) id Function.surjective_id
      (qCoordinateRiesz m)).norm.pow 2

theorem qCoordinateCapacity_gap (N m : ℕ) :
    walkError (fun i : ℕ => qResidue (i + 2)) id (qCoordinateRiesz m) N -
      limitingError (fun i : ℕ => qResidue (i + 2)) (qCoordinateRiesz m) =
        qCoordinateLimitCapacity m - qCoordinateCapacity N m := by
  have hn := nested_projection_energy (⊥ : Submodule ℝ QHilbert)
    (QFullResidueProjection.stage N) bot_le (qCoordinateRiesz m)
  have hl := nested_projection_energy (⊥ : Submodule ℝ QHilbert)
    QFullResidueProjection.closure bot_le (qCoordinateRiesz m)
  simp only [Submodule.starProjection_bot, ContinuousLinearMap.zero_apply, sub_zero] at hn hl
  change ‖qCoordinateRiesz m‖ ^ 2 =
    walkError (fun i : ℕ => qResidue (i + 2)) id (qCoordinateRiesz m) N +
      qCoordinateCapacity N m at hn
  change ‖qCoordinateRiesz m‖ ^ 2 =
    limitingError (fun i : ℕ => qResidue (i + 2)) (qCoordinateRiesz m) +
      qCoordinateLimitCapacity m at hl
  linarith

/-- Actual Q signed multiple coefficients have absolutely summable increments, unconditionally. -/
theorem q_packetCoordinate_variation_summable (N m : ℕ) (hm : 1 < m) :
    Summable (fun j => |QRamanujanCanonicalOptimizer.packetCoordinate (j + N + 1) m - QRamanujanCanonicalOptimizer.packetCoordinate (j + N) m|) := by
  have h := observation_variation_summable (fun i : ℕ => qResidue (i + 2)) id
    (qCoordinateRiesz m) qOne N
  simpa only [observation, qCoordinateRiesz_inner, QRamanujanCanonicalOptimizer.packetCoordinate_eq _ m hm,
    QRamanujanCanonicalOptimizer.packetCandidate_eq_residueCandidate, QFullResidueProjection.candidate_eq_projection,
    QFullResidueProjection.stage] using h

theorem q_packetCoordinate_variation_tail_sq_le (N m : ℕ) (hm : 1 < m) :
    (∑' j, |QRamanujanCanonicalOptimizer.packetCoordinate (j + N + 1) m - QRamanujanCanonicalOptimizer.packetCoordinate (j + N) m|) ^ 2 ≤
      (qCoordinateLimitCapacity m - qCoordinateCapacity N m) *
        (1 - QRamanujanCanonicalOptimizer.packetMass N - QRamanujanCanonicalOptimizer.packetLimitEnergy) := by
  have h := variation_tail_sq_le (fun i : ℕ => qResidue (i + 2)) id
    Function.surjective_id (qCoordinateRiesz m) qOne N
  rw [qCoordinateCapacity_gap] at h
  have he : walkError (fun i : ℕ => qResidue (i + 2)) id qOne N =
      1 - QRamanujanCanonicalOptimizer.packetMass N := by
    rw [← QRamanujanCanonicalOptimizer.packet_error]
    rw [QRamanujanCanonicalOptimizer.packetCandidate_eq_residueCandidate, QFullResidueProjection.candidate_eq_projection]
    rfl
  rw [he] at h
  simpa only [observation, qCoordinateRiesz_inner, QRamanujanCanonicalOptimizer.packetCoordinate_eq _ m hm,
    QRamanujanCanonicalOptimizer.packetCandidate_eq_residueCandidate, QFullResidueProjection.candidate_eq_projection,
    QFullResidueProjection.stage, QRamanujanCanonicalOptimizer.packetLimitEnergy, QFullResidueProjection.closure,
    QFullResidueProjection.legalSpan, dictionaryClosure, limitingError] using h

end RiemannResearch.RH.RamanujanCoordinateVariation
