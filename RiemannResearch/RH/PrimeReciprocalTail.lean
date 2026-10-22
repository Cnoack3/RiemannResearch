import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Removing finitely many primes preserves reciprocal divergence

A subtype-indexed version of Euler's theorem, with an arbitrary lower cutoff.
This supplies the final contradiction for the smooth-scale covariance bound.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Prime reciprocal sums still diverge after deleting every prime below `N`. -/
theorem not_summable_prime_reciprocal_tail (N : ℕ) :
    ¬ Summable (fun p : {p : ℕ // p.Prime ∧ N ≤ p} => (1 : ℝ) / (p.val : ℝ)) := by
  classical
  intro hs
  have hnat : Summable (fun n : ℕ => if n.Prime ∧ N ≤ n then (1 : ℝ)/(n : ℝ) else 0) := by
    have h := (summable_subtype_iff_indicator
      (f := fun n : ℕ => (1 : ℝ)/(n : ℝ))
      (s := {n : ℕ | n.Prime ∧ N ≤ n})).mp hs
    have he : ({n : ℕ | n.Prime ∧ N ≤ n}.indicator
        (fun n : ℕ => (1 : ℝ)/(n : ℝ))) =
        (fun n : ℕ => if n.Prime ∧ N ≤ n then (1 : ℝ)/(n : ℝ) else 0) := by
      funext n
      by_cases hn : n.Prime ∧ N ≤ n <;> simp [Set.indicator_apply, hn]
    rw [he] at h
    exact h
  have hshift : Summable
      (fun n : ℕ => if (n+N).Prime then (1 : ℝ)/((n+N : ℕ) : ℝ) else 0) := by
    have hinj : Function.Injective (fun n : ℕ => n+N) := by
      intro n m h
      exact Nat.add_right_cancel h
    have h := hnat.comp_injective hinj
    have he : ((fun n : ℕ => if n.Prime ∧ N ≤ n then (1 : ℝ)/(n : ℝ) else 0) ∘
        (fun n : ℕ => n+N)) =
        (fun n : ℕ => if (n+N).Prime then (1 : ℝ)/((n+N : ℕ) : ℝ) else 0) := by
      funext n
      simp only [Function.comp_apply, show N ≤ n+N from Nat.le_add_left N n, and_true]
    rw [he] at h
    exact h
  have hall : Summable (fun n : ℕ => if n.Prime then (1 : ℝ)/(n : ℝ) else 0) :=
    (summable_nat_add_iff N).mp hshift
  apply not_summable_one_div_on_primes
  have he : ({n : ℕ | n.Prime}.indicator (fun n : ℕ => (1 : ℝ)/(n : ℝ))) =
      (fun n : ℕ => if n.Prime then (1 : ℝ)/(n : ℝ) else 0) := by
    funext n
    by_cases hn : n.Prime <;> simp [Set.indicator_apply, hn]
  rw [he]
  exact hall

end
end RiemannResearch.RH.Pareto
