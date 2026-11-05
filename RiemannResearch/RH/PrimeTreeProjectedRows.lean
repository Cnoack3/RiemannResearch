import RiemannResearch.RH.QPrimeSubtreeBudget
import RiemannResearch.RH.QSquarefreeDisplacementRegularity
import RiemannResearch.RH.MobiusDifferenceCLM
import RiemannResearch.Analysis.DenseProjectionTesting
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # An exact projection test for an individual tree row

Source: the matched-projection agenda in C. Noack, *Prime trees, fractional
parts, and zeta zeros* (2026), §7. Project the finite charge row in Q, multiply
its physical entries by 1/n, and test against the fixed Pareto residual. -/

noncomputable section
open Filter Set
open scoped BigOperators
namespace RiemannResearch.RH.PrimeTreeProjectedRows
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer Pareto QPrimeSubtreeBudget
open ZetaTwoOptimizerStage QSquarefreeDisplacementRigidity QSquarefreeDisplacementRegularity
open QShiftedReciprocal QSquarefreeMeasureRigidity QParetoClosedProjectionComparison

/-- Physical Riesz vector of the finite subtree charge sum. -/
def subtreeRow (H r : ℕ) : QHilbert :=
  ∑ m ∈ Finset.Icc 1 H, if r ∈ prefixes m then
    (m : ℝ)⁻¹ • (InnerProductSpace.toDual ℝ QHilbert).symm
      ((mobiusDifferenceCLM m).comp toParetoCLM) else 0

theorem subtreeRow_inner (H r : ℕ) (f : QHilbert) :
    inner ℝ (subtreeRow H r) f = subtree (charge f) H r := by
  rw [subtreeRow, sum_inner, subtree]
  apply Finset.sum_congr rfl
  intro m _
  split_ifs with hm
  · rw [real_inner_smul_left, InnerProductSpace.toDual_symm_apply]
    simp [charge, div_eq_mul_inv, mul_comm]
  · simp

private theorem reciprocal_identity (u : QHilbert) :
    reciprocalD u - B (reciprocalD u) = B u := by
  ext n
  change u n / ((n : ℝ) + 1) - u n / ((n : ℝ) + 1) / ((n : ℝ) + 2) =
    u n / ((n : ℝ) + 2)
  field_simp [show (n : ℝ) + 1 ≠ 0 by positivity, show (n : ℝ) + 2 ≠ 0 by positivity]
  ring

/-- Every test vector admits a free legal comparison after applying the
compact multiplier 1/n to its Q projection. -/
theorem row_exact (W v : QHilbert) (hv : v ∈ ZetaTwoOptimizerStage.closure) :
    zetaTwo * inner ℝ W displacement =
      inner ℝ (toPareto (reciprocalD (ZetaTwoOptimizerStage.closure.starProjection W) - v))
        (toPareto pResidual) := by
  let u := ZetaTwoOptimizerStage.closure.starProjection W
  have hu := ZetaTwoOptimizerStage.closure.starProjection_apply_mem W
  have hProj : inner ℝ W displacement = inner ℝ u displacement := by
    simpa only [real_inner_comm displacement] using
      RiemannResearch.Analysis.DenseProjectionTesting.inner_eq_projected_test
        ZetaTwoOptimizerStage.closure displacement_mem W
  have hzero : inner ℝ (toPareto v) (toPareto pResidual) = 0 := by
    unfold pResidual
    rw [toPareto_sub, toPareto_pFit]
    exact Submodule.inner_right_of_mem_orthogonal
      (toPareto_mem_paretoSquarefreeClosure v hv)
      (Submodule.sub_starProjection_mem_orthogonal
        (K := paretoSquarefreeClosure) (toPareto qOne))
  rw [hProj, displacement_normal_equation u hu, ← B_symmetric, toPareto_sub,
    inner_sub_left, hzero, sub_zero, pareto_inner_identity]
  rw [← B_symmetric (reciprocalD u) pResidual, ← inner_sub_left, reciprocal_identity]

theorem subtree_row_bound (H r : ℕ) (v : QHilbert) (hv : v ∈ ZetaTwoOptimizerStage.closure) :
    |zetaTwo * subtree (charge displacement) H r| ≤
      ‖toPareto (reciprocalD (ZetaTwoOptimizerStage.closure.starProjection (subtreeRow H r)) - v)‖ *
        ‖toPareto pResidual‖ := by
  rw [← subtreeRow_inner, row_exact _ _ hv]
  exact abs_real_inner_le_norm _ _

end RiemannResearch.RH.PrimeTreeProjectedRows
