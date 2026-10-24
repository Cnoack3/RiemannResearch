import RiemannResearch.Analysis.ContractiveLogBudget
import Mathlib.Tactic.Positivity

/-!
# Exact threshold counts for positive finite products

Source: elementary logarithmic product algebra for the user's Ramanujan
continuation, 24 October 2026. The exact identity retains both the individual
threshold slack and the unused product mass before any count is bounded.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ContractiveLogBudget

theorem finite_count_budget_exact {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) {m c : ℝ} (hm : 0 < m) (hc : 0 < c) :
    -Real.log m = (S.card : ℝ) * (-Real.log c) +
      (∑ i ∈ S, Real.log (c / a i)) + Real.log ((∏ i ∈ S, a i) / m) := by
  rw [Real.log_div (Finset.prod_pos ha).ne' hm.ne',
    Real.log_prod (fun i hi => (ha i hi).ne')]
  have he : (∑ i ∈ S, Real.log (c / a i)) =
      (S.card : ℝ) * Real.log c - ∑ i ∈ S, Real.log (a i) := by
    calc
      _ = ∑ i ∈ S, (Real.log c - Real.log (a i)) :=
        Finset.sum_congr rfl (fun i hi => Real.log_div hc.ne' (ha i hi).ne')
      _ = _ := by simp [Finset.sum_sub_distrib, nsmul_eq_mul]
  rw [he]
  ring

theorem finite_count_log_bound {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) {m c : ℝ} (hm : 0 < m) (hc : 0 < c)
    (hac : ∀ i ∈ S, a i ≤ c) (hmass : m ≤ ∏ i ∈ S, a i) :
    (S.card : ℝ) * (-Real.log c) ≤ -Real.log m := by
  have he := finite_count_budget_exact S a ha hm hc
  have hs : 0 ≤ ∑ i ∈ S, Real.log (c / a i) := by
    apply Finset.sum_nonneg
    intro i hi
    exact Real.log_nonneg ((le_div_iff₀ (ha i hi)).mpr (by simpa using hac i hi))
  have hr : 0 ≤ Real.log ((∏ i ∈ S, a i) / m) :=
    Real.log_nonneg ((le_div_iff₀ hm).mpr (by simpa using hmass))
  linarith

theorem finite_count_product_bound {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) {m c : ℝ}
    (hac : ∀ i ∈ S, a i ≤ c) (hmass : m ≤ ∏ i ∈ S, a i) :
    m ≤ c ^ S.card := by
  exact hmass.trans (by simpa using Finset.prod_le_prod ha hac)

end RiemannResearch.Analysis.ContractiveLogBudget
