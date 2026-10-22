import RiemannResearch.RH.WeightedDivisorCorrection
import Mathlib.Analysis.PSeries

/-!
# Infinite weighted Mobius correction mass

Source: the user-requested three-route synthesis, 29 September 2026.
Finite divisor convolution and Pareto Cauchy--Schwarz give a bounded map
from the actual Hilbert space into weighted l1. Applying it to the complete
signed derivative correction proves convergence about its identified limit.
This does not assert vanishing of the limiting correction or RH.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.WeightedDivisorCorrection
open RiemannResearch.NumberTheory.WeightedDivisorTransform

def squareSeries : ℝ := ∑' k : ℕ, squareWeight k
def squareCubeSeries : ℝ := ∑' k : ℕ,
  (1 / (k : ℝ)^2 + 1 / (k : ℝ)^3)
def divisorNormConstant : ℝ := Real.sqrt (squareSeries^2 * squareCubeSeries)

theorem squareWeight_summable : Summable squareWeight := by
  change Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2)
  exact Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)

theorem squareCube_summable : Summable (fun k : ℕ =>
    1 / (k : ℝ)^2 + 1 / (k : ℝ)^3) := by
  exact (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)).add
    (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 3))

theorem squareWeight_nonneg (k : ℕ) : 0 ≤ squareWeight k := by
  exact one_div_nonneg.mpr (sq_nonneg _)

theorem squareCube_nonneg (k : ℕ) :
    0 ≤ 1 / (k : ℝ)^2 + 1 / (k : ℝ)^3 := by positivity

theorem divisorNormConstant_nonneg : 0 ≤ divisorNormConstant := Real.sqrt_nonneg _

theorem finite_hilbert_divisor_bound (f : ThresholdHilbert) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), squareWeight n *
      |divisorTransform (fun k => (ArithmeticFunction.moebius k : ℝ))
        (hilbertSequence f) n|) ≤ divisorNormConstant * ‖f‖ := by
  have hz : (∑ k ∈ Finset.range (N + 1), squareWeight k) ≤ squareSeries :=
    Summable.sum_le_tsum _ (fun k _ => squareWeight_nonneg k) squareWeight_summable
  have hb : (∑ k ∈ Finset.range (N + 1),
      (1 / (k : ℝ)^2 + 1 / (k : ℝ)^3)) ≤ squareCubeSeries :=
    Summable.sum_le_tsum _ (fun k _ => squareCube_nonneg k) squareCube_summable
  have he : (∑ k ∈ Finset.range (N + 1),
      positiveWeight k * (hilbertSequence f k)^2) ≤ ‖f‖^2 := by
    rw [hilbert_norm_weighted_sq]
    exact Summable.sum_le_tsum _
      (fun k _ => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
      (hilbertSequence_square_summable f)
  have hz0 : 0 ≤ squareSeries := tsum_nonneg squareWeight_nonneg
  have hb0 : 0 ≤ squareCubeSeries := tsum_nonneg squareCube_nonneg
  have hzn : 0 ≤ ∑ k ∈ Finset.range (N + 1), squareWeight k :=
    Finset.sum_nonneg (fun k _ => squareWeight_nonneg k)
  have hbn : 0 ≤ ∑ k ∈ Finset.range (N + 1),
      (1 / (k : ℝ)^2 + 1 / (k : ℝ)^3) :=
    Finset.sum_nonneg (fun k _ => squareCube_nonneg k)
  have hen : 0 ≤ ∑ k ∈ Finset.range (N + 1),
      positiveWeight k * (hilbertSequence f k)^2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
  have hm : 0 ≤ ∑ n ∈ Finset.range (N + 1), squareWeight n *
      |divisorTransform (fun k => (ArithmeticFunction.moebius k : ℝ))
        (hilbertSequence f) n| :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (squareWeight_nonneg k) (abs_nonneg _))
  have hzsq := (sq_le_sq₀ hzn hz0).mpr hz
  have hc : divisorNormConstant^2 = squareSeries^2 * squareCubeSeries :=
    Real.sq_sqrt (mul_nonneg (sq_nonneg _) hb0)
  apply (sq_le_sq₀ hm (mul_nonneg divisorNormConstant_nonneg (norm_nonneg _))).mp
  calc
    _ ≤ (∑ k ∈ Finset.range (N + 1), squareWeight k)^2 *
        (∑ k ∈ Finset.range (N + 1), positiveWeight k * (hilbertSequence f k)^2) *
          ∑ k ∈ Finset.range (N + 1),
            (1 / (k : ℝ)^2 + 1 / (k : ℝ)^3) :=
      finite_mobius_squareWeight_energy_bound (hilbertSequence f) N
    _ ≤ squareSeries^2 * ‖f‖^2 *
        ∑ k ∈ Finset.range (N + 1),
          (1 / (k : ℝ)^2 + 1 / (k : ℝ)^3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hzsq he hen (sq_nonneg _)) hbn
    _ ≤ squareSeries^2 * ‖f‖^2 * squareCubeSeries :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (divisorNormConstant * ‖f‖)^2 := by rw [mul_pow, hc]; ring

theorem hilbert_divisor_summable_and_bound (f : ThresholdHilbert) :
    Summable (fun n => squareWeight n *
      |divisorTransform (fun k => (ArithmeticFunction.moebius k : ℝ))
        (hilbertSequence f) n|) ∧
    (∑' n, squareWeight n *
      |divisorTransform (fun k => (ArithmeticFunction.moebius k : ℝ))
        (hilbertSequence f) n|) ≤ divisorNormConstant * ‖f‖ := by
  have hp (n : ℕ) : 0 ≤ squareWeight n *
      |divisorTransform (fun k => (ArithmeticFunction.moebius k : ℝ))
        (hilbertSequence f) n| :=
    mul_nonneg (squareWeight_nonneg n) (abs_nonneg _)
  have hb (N : ℕ) : (∑ n ∈ Finset.range N, squareWeight n *
      |divisorTransform (fun k => (ArithmeticFunction.moebius k : ℝ))
        (hilbertSequence f) n|) ≤ divisorNormConstant * ‖f‖ := by
    cases N with
    | zero => simpa using mul_nonneg divisorNormConstant_nonneg (norm_nonneg f)
    | succ N => exact finite_hilbert_divisor_bound f N
  exact ⟨summable_of_sum_range_le hp hb, Real.tsum_le_of_sum_range_le hp hb⟩

def weightedMobiusMass (f : ThresholdHilbert) : ℝ :=
  ∑' d, squareWeight d * |mobiusDifferenceCLM d f|

theorem weightedMobiusMass_le (f : ThresholdHilbert) :
    weightedMobiusMass f ≤ divisorNormConstant * ‖hilbertDifference f‖ := by
  simpa only [weightedMobiusMass, mobiusDifference_eq_derivative_divisorTransform] using
    (hilbert_divisor_summable_and_bound (hilbertDifference f)).2

open CoefficientStabilization CoefficientStabilization.GramMobiusCorrection
open CoefficientStabilization.DerivativeCompatibility

/-- The complete infinite coefficient mass of the actual signed correction
error; every finite coefficient and every limiting tail is included. -/
theorem correction_weightedMass_bound (n : ℕ) :
    weightedMobiusMass (correctionSynthesis n + limitResidual) ≤
      divisorNormConstant * (‖rawMobiusDerivativeResidual (n + 1)‖ +
        2 * ‖limitProjection - projection n‖) := by
  have hb := weightedMobiusMass_le (correctionSynthesis n + limitResidual)
  rw [map_add, correction_limit_error_exact] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    ((norm_sub_le _ _).trans (add_le_add_right (hilbertDifference_norm_le _) _))
    divisorNormConstant_nonneg)

theorem correction_weightedMass_tendsto_zero :
    Tendsto (fun n => weightedMobiusMass (correctionSynthesis n + limitResidual))
      atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => tsum_nonneg (fun d => mul_nonneg (squareWeight_nonneg d) (abs_nonneg _)))
    correction_weightedMass_bound
  simpa using correction_limit_budget_tendsto_zero.const_mul divisorNormConstant

end RiemannResearch.RH.Pareto.WeightedDivisorCorrection
