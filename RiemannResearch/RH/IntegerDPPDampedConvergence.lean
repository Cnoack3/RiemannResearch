import RiemannResearch.RH.IntegerDPPDampedLimit

/-!
# Existence and strict separation of the Pareto-damped occupied limit

Source: user-provided not-RH catalogue, group 26, 2026-09-21. This extends
the existing criterion for convergence to the RH benchmark: convergence
itself is unconditional, and under not RH the limit is strictly larger.
Only actual finite arithmetic determinants and their proved expectation
formulas are used. Operator Fredholm identification remains separate.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators Classical

namespace RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Probability.Occupancy

private def prefixProduct (m : ℕ) (x : ℕ → Bool) : ℝ :=
  ∏ i ∈ Finset.range m, if x i = true then 1 - paretoWeight i else 1

private theorem prefixProduct_eq (m : ℕ) (x : ℕ → Bool) :
    prefixProduct m x = product (fun i : Fin m => paretoWeight i.val)
      (fun i => x (prefixEmbedding m i)) := by
  unfold prefixProduct product prefixEmbedding
  exact (Fin.prod_univ_eq_prod_range
    (fun i : ℕ => if x i = true then 1 - paretoWeight i else 1) m).symm

private theorem prefixProduct_integrable (m : ℕ) :
    Integrable (prefixProduct m) limitingLaw := by
  have h := product_integrable limitingLaw (fun i : Fin m => paretoWeight i.val)
    (fun i => ⟨paretoWeight_pos i.val, paretoWeight_lt_one i.val⟩)
    (fun x i => x (prefixEmbedding m i))
    (measurable_pi_lambda _ (fun i => measurable_pi_apply (prefixEmbedding m i)))
  simpa only [← prefixProduct_eq] using h

private theorem prefixProduct_nonneg (m : ℕ) (x : ℕ → Bool) :
    0 ≤ prefixProduct m x := by
  apply Finset.prod_nonneg
  intro i hi
  split_ifs
  · linarith [paretoWeight_lt_one i]
  · norm_num

theorem dampedPrefixDeterminant_nonneg (m : ℕ) :
    0 ≤ dampedPrefixDeterminant m := by
  unfold dampedPrefixDeterminant
  rw [dampedWindowDeterminant_eq_integral]
  apply integral_nonneg
  intro x
  change 0 ≤ product (fun i : Fin m => paretoWeight i.val)
    (fun i => x (prefixEmbedding m i))
  rw [← prefixProduct_eq]
  exact prefixProduct_nonneg m x

theorem dampedPrefixDeterminant_antitone : Antitone dampedPrefixDeterminant := by
  apply antitone_nat_of_succ_le
  intro m
  have he (k : ℕ) : dampedPrefixDeterminant k = ∫ x, prefixProduct k x ∂limitingLaw := by
    unfold dampedPrefixDeterminant
    rw [dampedWindowDeterminant_eq_integral]
    simp only [← prefixProduct_eq]
  rw [he (m+1), he m]
  apply integral_mono (prefixProduct_integrable (m+1)) (prefixProduct_integrable m)
  intro x
  have hp := prefixProduct_nonneg m x
  change (∏ i ∈ Finset.range (m+1), if x i = true then 1 - paretoWeight i else 1) ≤ _
  rw [Finset.prod_range_succ]
  change prefixProduct m x * (if x m = true then 1 - paretoWeight m else 1) ≤ _
  split_ifs
  · nlinarith [mul_nonneg hp (paretoWeight_pos m).le]
  · simp

def dampedPrefixLimit : ℝ := ⨅ m : ℕ, dampedPrefixDeterminant m

theorem dampedPrefixDeterminant_tendsto :
    Tendsto dampedPrefixDeterminant atTop (𝓝 dampedPrefixLimit) := by
  have hb : BddBelow (Set.range dampedPrefixDeterminant) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact dampedPrefixDeterminant_nonneg m
  exact tendsto_atTop_ciInf dampedPrefixDeterminant_antitone hb

/-- A quantitative separation for the actual infinite-window limit. -/
theorem dampedPrefixLimit_lower :
    paretoProductBenchmark * (1 + limitingVacancy) ≤ dampedPrefixLimit := by
  have hb := (pareto_product_tendsto_benchmark.mul_const (1 + limitingVacancy)).comp
    (tendsto_add_atTop_nat 1)
  have hd := dampedPrefixDeterminant_tendsto.comp (tendsto_add_atTop_nat 1)
  exact le_of_tendsto_of_tendsto hb hd (Filter.Eventually.of_forall dampedPrefix_lower)

theorem benchmark_lt_dampedPrefixLimit_of_not_RH (h : ¬ RiemannHypothesis) :
    paretoProductBenchmark < dampedPrefixLimit := by
  have hv := limitingVacancy_pos_of_not_RH h
  have hp := paretoProductBenchmark_pos
  have hl := dampedPrefixLimit_lower
  nlinarith [mul_pos hp hv]

end RiemannResearch.RH.Pareto.IntegerDPP
