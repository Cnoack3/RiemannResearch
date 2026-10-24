import RiemannResearch.Analysis.WeightedCoordinateEnergy
import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.QRamanujanSaturationCriteria
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A single weighted Möbius-defect criterion in each actual measure

Source: fifth Ramanujan transfer program, 24 October 2026.
The weights are explicitly 2^(-j)/(1+‖coordinate_(j+2)‖²), hence positive
and summable. Every finite-stage and limiting defect is a convergent full
infinite sum. The uniform geometric tail bound is proved from the actual
Hilbert residual bounds. The scalar limit is unconditional; identifying
it as zero is exactly the still-open saturation/RH criterion.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanWeightedDefect
open Pareto ZetaTwoHilbert SquarefreeMobiusProjection
open RiemannResearch.Analysis.WeightedCoordinateEnergy

def paretoCoordinates (j : ℕ) : ThresholdHilbert →L[ℝ] ℝ :=
  CoefficientStabilization.coefficientCLM (j + 2)

def qCoordinates (j : ℕ) : QHilbert →L[ℝ] ℝ := qCoefficientCLM (j + 2)

def paretoDefect (n : ℕ) : ℝ :=
  energy paretoCoordinates (hilbertOne - CoefficientStabilization.projection n)

def paretoLimitDefect : ℝ := energy paretoCoordinates CoefficientStabilization.limitResidual

def qDefect (n : ℕ) : ℝ :=
  energy qCoordinates (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)

def qLimitDefect : ℝ :=
  energy qCoordinates (qOne - QFullResidueProjection.closure.starProjection qOne)

theorem pareto_coordinate_residual (n j : ℕ) :
    paretoCoordinates j (hilbertOne - CoefficientStabilization.projection n) =
      -(RamanujanCanonicalOptimizer.packetMultipleCoefficient n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) := by
  rw [RamanujanCanonicalOptimizer.packetMultipleCoefficient_eq _ _ (by omega)]
  simp only [paretoCoordinates, map_sub, CoefficientStabilization.coefficient,
    CoefficientStabilization.coefficientCLM, ContinuousLinearMap.neg_apply,
    mobius_coordinate_one (j + 2) (by omega)]
  ring

theorem q_coordinate_residual (n j : ℕ) :
    qCoordinates j (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) =
      -(QRamanujanCanonicalOptimizer.packetCoordinate n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) := by
  rw [QRamanujanCanonicalOptimizer.packetCoordinate_eq _ _ (by omega)]
  simp only [qCoordinates, map_sub, q_target_coordinate (j + 2) (by omega)]
  ring

theorem paretoDefect_series (n : ℕ) :
    paretoDefect n = ∑' j, weight paretoCoordinates j *
      (RamanujanCanonicalOptimizer.packetMultipleCoefficient n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) ^ 2 := by
  simp only [paretoDefect, energy, pareto_coordinate_residual, neg_sq]

theorem qDefect_series (n : ℕ) :
    qDefect n = ∑' j, weight qCoordinates j *
      (QRamanujanCanonicalOptimizer.packetCoordinate n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) ^ 2 := by
  simp only [qDefect, energy, q_coordinate_residual, neg_sq]

theorem pareto_residual_bound (n : ℕ) :
    ‖hilbertOne - CoefficientStabilization.projection n‖ ^ 2 ≤ 1 := by
  rw [← RamanujanCanonicalOptimizer.packetCandidate_eq_projection,
    RamanujanCanonicalOptimizer.packet_error]
  linarith [(RamanujanCanonicalOptimizer.packetMass_bounds n).1]

theorem q_residual_bound (n : ℕ) :
    ‖qOne - QRamanujanCanonicalOptimizer.packetCandidate n‖ ^ 2 ≤ 1 := by
  rw [QRamanujanCanonicalOptimizer.packet_error]
  change QRamanujanCanonicalOptimizer.packetError n ≤ 1
  rw [← QRamanujanCanonicalOptimizer.packetError_zero]
  exact QRamanujanCanonicalOptimizer.packetError_antitone (Nat.zero_le n)

/-- The same explicit geometric majorant works at every Pareto stage. -/
theorem pareto_defect_summand_bound (n j : ℕ) :
    weight paretoCoordinates j *
      (RamanujanCanonicalOptimizer.packetMultipleCoefficient n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) ^ 2 ≤ (1 / 2 : ℝ) ^ j := by
  have h := (summand_bound paretoCoordinates
    (hilbertOne - CoefficientStabilization.projection n) j).trans
      (mul_le_mul_of_nonneg_left (pareto_residual_bound n) (by positivity))
  simpa only [pareto_coordinate_residual, neg_sq, mul_one] using h

theorem q_defect_summand_bound (n j : ℕ) :
    weight qCoordinates j *
      (QRamanujanCanonicalOptimizer.packetCoordinate n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) ^ 2 ≤ (1 / 2 : ℝ) ^ j := by
  have h := (summand_bound qCoordinates
    (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) j).trans
      (mul_le_mul_of_nonneg_left (q_residual_bound n) (by positivity))
  simpa only [q_coordinate_residual, neg_sq, mul_one] using h

theorem pareto_defect_series_summable (n : ℕ) :
    Summable (fun j => weight paretoCoordinates j *
      (RamanujanCanonicalOptimizer.packetMultipleCoefficient n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) ^ 2) := by
  simpa only [pareto_coordinate_residual, neg_sq] using
    summand_summable paretoCoordinates (hilbertOne - CoefficientStabilization.projection n)

theorem q_defect_series_summable (n : ℕ) :
    Summable (fun j => weight qCoordinates j *
      (QRamanujanCanonicalOptimizer.packetCoordinate n (j + 2) +
        (ArithmeticFunction.moebius (j + 2) : ℝ)) ^ 2) := by
  simpa only [q_coordinate_residual, neg_sq] using
    summand_summable qCoordinates (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)

/-- A finite conductor-head evaluation has a certified uniform error of at most 2^(1-J). -/
theorem pareto_defect_uniform_tail (n J : ℕ) :
    (∑' j, weight paretoCoordinates (j + J) *
      (RamanujanCanonicalOptimizer.packetMultipleCoefficient n (j + J + 2) +
        (ArithmeticFunction.moebius (j + J + 2) : ℝ)) ^ 2) ≤ 2 * (1 / 2 : ℝ) ^ J := by
  have h := (tail_le paretoCoordinates
    (hilbertOne - CoefficientStabilization.projection n) J).trans
      (mul_le_mul_of_nonneg_left (pareto_residual_bound n) (by positivity))
  simpa only [pareto_coordinate_residual, neg_sq, mul_one] using h

theorem q_defect_uniform_tail (n J : ℕ) :
    (∑' j, weight qCoordinates (j + J) *
      (QRamanujanCanonicalOptimizer.packetCoordinate n (j + J + 2) +
        (ArithmeticFunction.moebius (j + J + 2) : ℝ)) ^ 2) ≤ 2 * (1 / 2 : ℝ) ^ J := by
  have h := (tail_le qCoordinates
    (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) J).trans
      (mul_le_mul_of_nonneg_left (q_residual_bound n) (by positivity))
  simpa only [q_coordinate_residual, neg_sq, mul_one] using h

theorem paretoDefect_tendsto : Tendsto paretoDefect atTop (𝓝 paretoLimitDefect) := by
  apply energy_tendsto_of_coordinates paretoCoordinates
    (fun n => hilbertOne - CoefficientStabilization.projection n)
    CoefficientStabilization.limitResidual
  · intro j
    exact ((paretoCoordinates j).continuous.tendsto _).comp
      (tendsto_const_nhds.sub CoefficientStabilization.projection_tendsto)
  · exact Eventually.of_forall pareto_residual_bound

theorem qDefect_tendsto : Tendsto qDefect atTop (𝓝 qLimitDefect) := by
  apply energy_tendsto_of_coordinates qCoordinates
    (fun n => qOne - QRamanujanCanonicalOptimizer.packetCandidate n)
    (qOne - QFullResidueProjection.closure.starProjection qOne)
  · intro j
    exact ((qCoordinates j).continuous.tendsto _).comp
      (tendsto_const_nhds.sub QRamanujanCanonicalOptimizer.packetCandidate_tendsto_projection)
  · exact Eventually.of_forall q_residual_bound

theorem paretoLimitDefect_zero_iff :
    paretoLimitDefect = 0 ↔ CoefficientStabilization.limitEnergy = 0 := by
  rw [paretoLimitDefect, energy_eq_zero_iff,
    ← CoefficientStabilization.limitResidual_zero_iff_energy_zero]
  constructor
  · intro h
    apply eq_zero_of_mobius_coordinates_zero
    intro m hm
    have hi := h (m - 2)
    have he : m - 2 + 2 = m := by omega
    simpa only [paretoCoordinates, he, CoefficientStabilization.coefficientCLM,
      ContinuousLinearMap.neg_apply, neg_eq_zero] using hi
  · intro h j
    simp only [h, map_zero]

theorem qLimitDefect_zero_iff :
    qLimitDefect = 0 ↔ QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 := by
  rw [qLimitDefect, energy_eq_zero_iff, QRamanujanCanonicalOptimizer.packetLimitEnergy,
    sq_eq_zero_iff, norm_eq_zero]
  constructor
  · intro h
    exact QTriangularCharge.q_eq_zero_of_all_coefficients_zero _ h
  · intro h j
    simp only [h, map_zero]

theorem paretoDefect_cofinal_zero_iff {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => paretoDefect (N i)) l (𝓝 0) ↔
      CoefficientStabilization.limitEnergy = 0 := by
  rw [← paretoLimitDefect_zero_iff]
  constructor
  · exact fun h => tendsto_nhds_unique (paretoDefect_tendsto.comp hN) h
  · intro h
    simpa only [h, Function.comp_def] using paretoDefect_tendsto.comp hN

theorem qDefect_cofinal_zero_iff {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => qDefect (N i)) l (𝓝 0) ↔
      QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 := by
  rw [← qLimitDefect_zero_iff]
  constructor
  · exact fun h => tendsto_nhds_unique (qDefect_tendsto.comp hN) h
  · intro h
    simpa only [h, Function.comp_def] using qDefect_tendsto.comp hN

/-- Each complete infinite coefficient array is compressed into one exact scalar RH criterion. -/
theorem weighted_defect_rh_equivalences
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l] (N : α → ℕ) (hN : Tendsto N l atTop) :
    (Tendsto (fun i => paretoDefect (N i)) l (𝓝 0) ↔ RiemannHypothesis) ∧
      (Tendsto (fun i => qDefect (N i)) l (𝓝 0) ↔ RiemannHypothesis) := by
  have hp := (RamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
    (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1
  have hq := (QRamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
    (QRamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1
  exact ⟨(paretoDefect_cofinal_zero_iff N hN).trans hp,
    (qDefect_cofinal_zero_iff N hN).trans hq⟩

end RiemannResearch.RH.RamanujanWeightedDefect
