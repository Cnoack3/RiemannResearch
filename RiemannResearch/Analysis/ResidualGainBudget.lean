import RiemannResearch.Analysis.ResidualGainProduct

/-!
# Finite residual floors and quantitative gain budgets

Source: user-provided consolidated zero-ordinate/residual note (2026-10-11),
Sections 5--6, and the exact recurrence deduction in this continuation.
This cohesive extension keeps the original gain-product module unchanged.
The declarations and proofs are moved without mathematical changes.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.ResidualGain

theorem log_gain_sum_eq_log_ratio {d r : ℕ → ℝ} (hd : 0 < d 0)
    (h1 : ∀ n, r n < 1)
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n)) (N : ℕ) :
    (∑ n ∈ Finset.range N, -Real.log (1 - r n)) = Real.log (d 0 / d N) := by
  rw [Real.log_div (ne_of_gt hd) (ne_of_gt (recurrence_pos hd h1 hrec N))]
  linarith [log_recurrence_eq_initial_sub_sum hd h1 hrec N]

theorem log_gain_sum_le_log_budget {d r : ℕ → ℝ} (hd : 0 < d 0)
    (h1 : ∀ n, r n < 1)
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n))
    (N : ℕ) {L : ℝ} (hL : 0 < L) (hlower : L ≤ d N) :
    (∑ n ∈ Finset.range N, -Real.log (1 - r n)) ≤ Real.log (d 0 / L) := by
  rw [log_gain_sum_eq_log_ratio hd h1 hrec N]
  apply Real.log_le_log (div_pos hd (recurrence_pos hd h1 hrec N))
  exact div_le_div_of_nonneg_left hd.le hL hlower

theorem gain_sum_le_log_budget {d r : ℕ → ℝ} (hd : 0 < d 0)
    (h1 : ∀ n, r n < 1)
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n))
    (N : ℕ) {L : ℝ} (hL : 0 < L) (hlower : L ≤ d N) :
    (∑ n ∈ Finset.range N, r n) ≤ Real.log (d 0 / L) := by
  exact (Finset.sum_le_sum (fun n _ => gain_le_neg_log_one_sub (h1 n))).trans
    (log_gain_sum_le_log_budget hd h1 hrec N hL hlower)

end RiemannResearch.Analysis.ResidualGain
