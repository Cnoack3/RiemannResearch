import RiemannResearch.RH.IntegerDPPWeightedVacancy
import RiemannResearch.Probability.MultiplicativeOccupancy

/-!
# Quantitative Pareto determinant separation by weighted vacancy

Source: user-provided DPP coupling/Mellin/Fredholm/cutoff argument,
RH_DPP_Coupling_Mellin_Fredholm_and_Cutoff_Bounds_2026-09-21.md,
Sections 6--8. The product comparison developed in ContractiveProducts
and MultiplicativeOccupancy gives an additive determinant comparison.

The observation cutoff M is applied to the actual limiting arithmetic
kernel. It is distinct from the finite arithmetic projection rank N.
The exact product expectation retains all correlations. Convergence and
the two-sided comparison are unconditional. Full operator Fredholm
identification and the sharper logarithmic comparison remain separate.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators Classical

namespace RiemannResearch.RH.Pareto.IntegerDPP
open HistoricalTargets
open RiemannResearch.Probability.Occupancy

def limitingWeightedVacancyPrefix (M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range M, paretoWeight i * (1 - limitingKernel i i)

/-- Exact finite expectation, retaining every correlation in the product. -/
theorem dampedPrefixDefect_eq_integral (M : ℕ) :
    dampedPrefixDeterminant M - (∏ i ∈ Finset.range M, (1 - paretoWeight i)) =
      ∫ x, product (fun i : Fin M => paretoWeight i.val)
        (fun i => x (prefixEmbedding M i)) -
        benchmark (fun i : Fin M => paretoWeight i.val) ∂limitingLaw := by
  have hint := product_integrable limitingLaw (fun i : Fin M => paretoWeight i.val)
    (fun i => ⟨paretoWeight_pos i.val, paretoWeight_lt_one i.val⟩)
    (fun x i => x (prefixEmbedding M i))
    (measurable_pi_lambda _ (fun i => measurable_pi_apply (prefixEmbedding M i)))
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul,
    ← dampedWindowDeterminant_eq_integral]
  unfold benchmark
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => 1 - paretoWeight i) M]
  rfl

theorem dampedPrefixDeterminant_defect_bounds (M : ℕ) :
    (∏ i ∈ Finset.range M, (1 - paretoWeight i)) * limitingWeightedVacancyPrefix M ≤
      dampedPrefixDeterminant M - (∏ i ∈ Finset.range M, (1 - paretoWeight i)) ∧
    dampedPrefixDeterminant M - (∏ i ∈ Finset.range M, (1 - paretoWeight i)) ≤
      limitingWeightedVacancyPrefix M := by
  have h := integral_product_defect_bounds limitingLaw
    (fun i : Fin M => paretoWeight i.val)
    (fun i => ⟨paretoWeight_pos i.val, paretoWeight_lt_one i.val⟩)
    (fun x i => x (prefixEmbedding M i))
    (measurable_pi_lambda _ (fun i => measurable_pi_apply (prefixEmbedding M i)))
  have he : (∫ x, product (fun i : Fin M => paretoWeight i.val)
      (fun i => x (prefixEmbedding M i)) ∂limitingLaw) =
      dampedPrefixDeterminant M :=
    (dampedWindowDeterminant_eq_integral M (prefixEmbedding M)
      (fun i => paretoWeight i.val)).symm
  have hb : benchmark (fun i : Fin M => paretoWeight i.val) =
      ∏ i ∈ Finset.range M, (1 - paretoWeight i) :=
    Fin.prod_univ_eq_prod_range (fun i : ℕ => 1 - paretoWeight i) M
  have hv (i : Fin M) :
      limitingLaw.real {x | x (prefixEmbedding M i) = false} =
        1 - limitingKernel i.val i.val := by
    simpa [prefixEmbedding] using limitingLaw_isDPP.vacancy i.val
  have hm :
      (∑ i : Fin M, paretoWeight i.val *
        limitingLaw.real {x | x (prefixEmbedding M i) = false}) =
        limitingWeightedVacancyPrefix M := by
    simp_rw [hv]
    exact Fin.sum_univ_eq_sum_range
      (fun i : ℕ => paretoWeight i * (1 - limitingKernel i i)) M
  rw [he, hb, hm] at h
  exact h

theorem limitingWeightedVacancyPrefix_tendsto :
    Tendsto limitingWeightedVacancyPrefix atTop (𝓝 weightedVacancyMass) :=
  weightedVacancyMass_summable.hasSum.tendsto_sum_nat

/-- An unconditional quantitative comparison for the actual limiting value.
This does not identify an infinite-dimensional operator Fredholm determinant. -/
theorem dampedPrefixLimit_defect_bounds :
    paretoProductBenchmark * weightedVacancyMass ≤
      dampedPrefixLimit - paretoProductBenchmark ∧
    dampedPrefixLimit - paretoProductBenchmark ≤ weightedVacancyMass := by
  have hd := dampedPrefixDeterminant_tendsto.sub pareto_product_tendsto_benchmark
  constructor
  · exact le_of_tendsto_of_tendsto
      (pareto_product_tendsto_benchmark.mul limitingWeightedVacancyPrefix_tendsto) hd
      (Eventually.of_forall (fun M => (dampedPrefixDeterminant_defect_bounds M).1))
  · exact le_of_tendsto_of_tendsto hd limitingWeightedVacancyPrefix_tendsto
      (Eventually.of_forall (fun M => (dampedPrefixDeterminant_defect_bounds M).2))

theorem weightedVacancyMass_zero_iff_dampedPrefixLimit_eq_benchmark :
    weightedVacancyMass = 0 ↔ dampedPrefixLimit = paretoProductBenchmark := by
  have hb := dampedPrefixLimit_defect_bounds
  constructor
  · intro h
    rw [h] at hb
    linarith
  · intro h
    rw [h] at hb
    have hp := paretoProductBenchmark_pos
    have hm := weightedVacancyMass_bounds.1
    nlinarith

end RiemannResearch.RH.Pareto.IntegerDPP
