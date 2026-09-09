import RiemannResearch.RH.FiniteTwoSeedHeadMean

/-!
# The genuine two-parameter constrained error and monotonicity in the budget

Source: advanced covariance repair report, Section 7.7. The head length is held
fixed while the independent dilation budget increases. These definitions use
the actual full infinite Pareto error, with exact head and mean constraints.
-/

namespace RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion
noncomputable section

/-- Squared approximation error against the complete positive Pareto law. -/
def completeError (f : ℕ → ℝ) : ℝ :=
  paretoInner (fun k => 1 - f k) (fun k => 1 - f k)

theorem completeError_nonneg (f : ℕ → ℝ) : 0 ≤ completeError f :=
  paretoInner_self_nonneg _

/-- Actual attainable errors with independent head and budget parameters. -/
def budgetErrors (H M : ℕ) : Set ℝ :=
  {e | ∃ f ∈ budgetSpan M,
    (∀ k, 0 < k → k ≤ H → f k = 1) ∧ paretoMean f = 1 ∧ e = completeError f}

theorem budgetErrors_nonempty (H M : ℕ) (hH : 0 < H) (hHM : H ≤ M) :
    (budgetErrors H M).Nonempty := by
  obtain ⟨f, hf, hhead, hmean⟩ := exists_head_mean_of_le (fun _ => 1) 1 H M hH hHM
  exact ⟨completeError f, f, hf, hhead, hmean, rfl⟩

theorem budgetErrors_bddBelow (H M : ℕ) : BddBelow (budgetErrors H M) := by
  refine ⟨0, ?_⟩
  rintro e ⟨f, hf, hhead, hmean, rfl⟩
  exact completeError_nonneg f

theorem budgetErrors_mono (H : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    budgetErrors H M ⊆ budgetErrors H N := by
  rintro e ⟨f, hf, hhead, hmean, he⟩
  exact ⟨f, budgetSpan_mono hMN hf, hhead, hmean, he⟩

/-- The infimum of the exact constrained errors; no vanishing limit is asserted. -/
def budgetErrorInfimum (H M : ℕ) : ℝ := sInf (budgetErrors H M)

theorem budgetErrorInfimum_nonneg (H M : ℕ) (hH : 0 < H) (hHM : H ≤ M) :
    0 ≤ budgetErrorInfimum H M := by
  apply le_csInf (budgetErrors_nonempty H M hH hHM)
  rintro e ⟨f, hf, hhead, hmean, rfl⟩
  exact completeError_nonneg f

theorem budgetErrorInfimum_le (H M : ℕ) (f : ℕ → ℝ)
    (hf : f ∈ budgetSpan M) (hhead : ∀ k, 0 < k → k ≤ H → f k = 1)
    (hmean : paretoMean f = 1) :
    budgetErrorInfimum H M ≤ completeError f := by
  exact csInf_le (budgetErrors_bddBelow H M) ⟨f, hf, hhead, hmean, rfl⟩

/-- Increasing the budget decreases the genuine constrained error infimum. -/
theorem budgetErrorInfimum_antitone (H M N : ℕ) (hH : 0 < H)
    (hHM : H ≤ M) (hMN : M ≤ N) :
    budgetErrorInfimum H N ≤ budgetErrorInfimum H M := by
  apply le_csInf (budgetErrors_nonempty H M hH hHM)
  intro e he
  exact csInf_le (budgetErrors_bddBelow H N) (budgetErrors_mono H hMN he)

/-- Arbitrarily accurate exact constraints may be expressed in finite budgets
or in the full algebraic two-seed span, with no loss of any integer dilation. -/
theorem exact_approximation_iff_budget (H : ℕ) :
    (∀ ε : ℝ, 0 < ε → ∃ f ∈ legalSeedSpan ({2, 3} : Set ℕ),
      (∀ k, 0 < k → k ≤ H → f k = 1) ∧ paretoMean f = 1 ∧ completeError f < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ M, H ≤ M ∧ ∃ f ∈ budgetSpan M,
      (∀ k, 0 < k → k ≤ H → f k = 1) ∧ paretoMean f = 1 ∧ completeError f < ε) := by
  constructor
  · intro h ε hε
    obtain ⟨f, hf, hhead, hmean, herr⟩ := h ε hε
    obtain ⟨M, hM⟩ := (mem_legal_iff_exists_budget f).mp hf
    exact ⟨max H M, le_max_left H M, f,
      budgetSpan_mono (le_max_right H M) hM, hhead, hmean, herr⟩
  · intro h ε hε
    obtain ⟨M, hHM, f, hf, hhead, hmean, herr⟩ := h ε hε
    exact ⟨f, budgetSpan_le_legal M hf, hhead, hmean, herr⟩

end
end RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion
