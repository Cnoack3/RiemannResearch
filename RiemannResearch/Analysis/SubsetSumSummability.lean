import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Absolute summability from bounded finite subset sums

Source: the user's canonical prime coefficient summability request,
12 November 2026. The finite positive/negative split keeps both signed sums.
The RH application is QPrimeCoefficientSummability.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.SubsetSumSummability

theorem sum_abs_eq_positive_sub_negative {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ s, |a i|) =
      (∑ i ∈ s.filter (fun i => 0 ≤ a i), a i) -
      ∑ i ∈ s.filter (fun i => a i < 0), a i := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : 0 ≤ a i
  · simp [h, not_lt.mpr h, abs_of_nonneg h]
  · have hn : a i < 0 := lt_of_not_ge h
    simp [h, hn, abs_of_neg hn]

theorem sum_abs_le_of_subset_sum_bounds {ι : Type*}
    (a : ι → ℝ) (L U : ℝ)
    (h : ∀ s : Finset ι, L ≤ ∑ i ∈ s, a i ∧ ∑ i ∈ s, a i ≤ U)
    (s : Finset ι) :
    ∑ i ∈ s, |a i| ≤ U - L := by
  classical
  rw [sum_abs_eq_positive_sub_negative]
  exact sub_le_sub (h _).2 (h _).1

theorem summable_abs_of_subset_sum_bounds {ι : Type*}
    (a : ι → ℝ) (L U : ℝ)
    (h : ∀ s : Finset ι, L ≤ ∑ i ∈ s, a i ∧ ∑ i ∈ s, a i ≤ U) :
    Summable (fun i => |a i|) := by
  exact summable_of_sum_le (fun i => abs_nonneg (a i))
    (sum_abs_le_of_subset_sum_bounds a L U h)

theorem tsum_abs_le_of_subset_sum_bounds {ι : Type*}
    (a : ι → ℝ) (L U : ℝ)
    (h : ∀ s : Finset ι, L ≤ ∑ i ∈ s, a i ∧ ∑ i ∈ s, a i ≤ U) :
    ∑' i, |a i| ≤ U - L := by
  exact le_of_tendsto (summable_abs_of_subset_sum_bounds a L U h).hasSum
    (Filter.Eventually.of_forall (sum_abs_le_of_subset_sum_bounds a L U h))

end RiemannResearch.Analysis.SubsetSumSummability
