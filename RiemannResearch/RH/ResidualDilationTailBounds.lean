import RiemannResearch.RH.ResidualDilationPartialSums
import RiemannResearch.RH.ParetoDilationTailLocalization

/-!
# Tail-sensitive bounds for the actual residual dilation correlations

Source: `RH/Residual_Abel_Obstruction_20260924.md`, Section 1.
These specialize support localization to the actual orthogonal residual
and its exact signed partial-sum identity. No novelty is claimed.

The normalized squared correlation tends to zero unconditionally.
The finite primitive bound retains every residual tail. No sublinear
primitive estimate or vanishing of the full residual energy is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
namespace CoefficientStabilization

theorem residual_dilation_pairing_sq_le_tail (N : ℕ) :
    (inner ℝ limitResidual
      (hilbertDilation (N + 1) (by omega) limitResidual)) ^ 2 ≤
      ((N : ℝ) + 1) * limitEnergy * residualTailEnergy N :=
  hilbertDilation_pairing_sq_le_tail limitResidual limitResidual N

theorem residual_dilation_pairing_abs_le_tail (N : ℕ) :
    |inner ℝ limitResidual
      (hilbertDilation (N + 1) (by omega) limitResidual)| ≤
      Real.sqrt (((N : ℝ) + 1) * limitEnergy * residualTailEnergy N) := by
  have h := Real.sqrt_le_sqrt (residual_dilation_pairing_sq_le_tail N)
  simpa only [Real.sqrt_sq_eq_abs] using h

theorem residual_dilation_normalized_pairing_sq_tendsto_zero :
    Tendsto (fun N : ℕ =>
      (inner ℝ limitResidual
        (hilbertDilation (N + 1) (by omega) limitResidual)) ^ 2 /
        ((N : ℝ) + 1)) atTop (𝓝 0) :=
  hilbertDilation_normalized_pairing_sq_tendsto_zero limitResidual limitResidual

theorem residual_partial_sum_abs_le_tail (N : ℕ) :
    |∑ k ∈ Finset.range N, hilbertSequence limitResidual (k + 1)| ≤
      2 * (∑ k ∈ Finset.range N,
        Real.sqrt (((k : ℝ) + 1) * limitEnergy * residualTailEnergy k)) +
      (N : ℝ) * Real.sqrt
        (((N : ℝ) + 1) * limitEnergy * residualTailEnergy N) := by
  have hs :
      |∑ k ∈ Finset.range N,
        inner ℝ limitResidual
          (hilbertDilation (k + 1) (by omega) limitResidual)| ≤
      ∑ k ∈ Finset.range N,
        Real.sqrt (((k : ℝ) + 1) * limitEnergy * residualTailEnergy k) := by
    calc
      _ ≤ ∑ k ∈ Finset.range N,
          |inner ℝ limitResidual
            (hilbertDilation (k + 1) (by omega) limitResidual)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum (fun k _ => residual_dilation_pairing_abs_le_tail k)
  have hl := residual_dilation_pairing_abs_le_tail N
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlo := mul_le_mul_of_nonneg_left (abs_le.mp hl).1 hN
  have hhi := mul_le_mul_of_nonneg_left (abs_le.mp hl).2 hN
  rw [residual_partial_sum_dilation_identity]
  apply abs_le.mpr
  constructor <;> nlinarith [(abs_le.mp hs).1, (abs_le.mp hs).2, hlo, hhi]

end CoefficientStabilization
end RiemannResearch.RH.Pareto
