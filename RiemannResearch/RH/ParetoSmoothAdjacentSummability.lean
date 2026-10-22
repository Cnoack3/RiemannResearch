import RiemannResearch.RH.ParetoDisjointRepairSummability
import RiemannResearch.RH.ParetoRepairAnchorCancellation
import RiemannResearch.RH.Smooth35Choice

/-!
# Unconditional summability of the least-smooth cluster replacement family

Source: `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`, §5.
The endpoint is the next chosen integer until the next smooth scale is reached;
the last member of each cluster retains its original smooth anchor. The complete
variance sum converges by the telescoping modulus, without a smooth-gap theorem.
The result applies in particular when `p` enumerates the primes at least seven.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Between an integer and its least smooth anchor, the least anchor is unchanged. -/
theorem leastSmooth35Above_eq_of_between {p q : ℕ}
    (hpq : p ≤ q) (hqE : q < leastSmooth35Above p) :
    leastSmooth35Above q = leastSmooth35Above p := by
  apply Nat.le_antisymm
  · exact leastSmooth35Above_le hqE (leastSmooth35Above_spec p).2
  · exact leastSmooth35Above_le
      (lt_of_le_of_lt hpq (leastSmooth35Above_spec q).1)
      (leastSmooth35Above_spec q).2

/-- The actual new endpoint after cancellation inside each smooth-scale cluster. -/
def smooth35SuccessorEndpoint (p : ℕ → ℕ) (i : ℕ) : ℕ :=
  min (leastSmooth35Above (p i)) (p (i + 1))

/-- The adjacent replacement keeps the old smooth anchor at the end of a cluster. -/
def smooth35SuccessorRepair (p : ℕ → ℕ) (i : ℕ) : ℕ → ℝ :=
  arithmeticRepair 2 (p i) (smooth35SuccessorEndpoint p i)

theorem smooth35SuccessorEndpoint_spec (p : ℕ → ℕ)
    (hmono : StrictMono p) (hp : ∀ i, 3 ≤ p i) (i : ℕ) :
    p i < smooth35SuccessorEndpoint p i ∧
      smooth35SuccessorEndpoint p i ≤ 2 * p i ∧
      smooth35SuccessorEndpoint p i ≤ p (i + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact lt_min (leastSmooth35Above_spec (p i)).1 (hmono (by omega))
  · exact (min_le_left _ _).trans (leastSmooth35Above_le_twice (p i) (hp i))
  · exact min_le_right _ _

/-- For an interior cluster member, the replacement is the exact shared-anchor
cancellation. Its neighboring prime term is retained with its signed coefficient. -/
theorem smooth35SuccessorRepair_interior (p : ℕ → ℕ)
    (hmono : StrictMono p) (hp : ∀ i, 0 < p i) (i k : ℕ)
    (hint : p (i + 1) < leastSmooth35Above (p i)) :
    smooth35SuccessorRepair p i k =
      arithmeticRepair 2 (p i) (leastSmooth35Above (p i)) k -
      ((p (i + 1) : ℝ) / (p i : ℝ)) *
        arithmeticRepair 2 (p (i + 1)) (leastSmooth35Above (p (i + 1))) k := by
  have he := leastSmooth35Above_eq_of_between (hmono (by omega)).le hint
  rw [he]
  unfold smooth35SuccessorRepair smooth35SuccessorEndpoint
  rw [min_eq_right hint.le]
  exact (arithmeticRepair_common_anchor_cancel 2 (p i) (p (i + 1))
    (leastSmooth35Above (p i)) k (hp i) (hp (i + 1))).symm

/-- The terminal member of each cluster is exactly its original smooth repair. -/
theorem smooth35SuccessorRepair_terminal (p : ℕ → ℕ) (i : ℕ)
    (hterm : leastSmooth35Above (p i) ≤ p (i + 1)) :
    smooth35SuccessorRepair p i =
      arithmeticRepair 2 (p i) (leastSmooth35Above (p i)) := by
  simp only [smooth35SuccessorRepair, smooth35SuccessorEndpoint, min_eq_left hterm]

/-- Unconditional summability for the actual replacement family, including every
terminal member. The indexing sequence needs only be increasing and start at three. -/
theorem summable_smooth35SuccessorRepair_variance (p : ℕ → ℕ)
    (hmono : StrictMono p) (hp : ∀ i, 3 ≤ p i) :
    Summable (fun i => paretoVariance (smooth35SuccessorRepair p i)) := by
  exact summable_ordered_disjoint_arithmeticRepair_variance
    p (smooth35SuccessorEndpoint p) (fun i => by have := hp i; omega)
    (fun i => (smooth35SuccessorEndpoint_spec p hmono hp i).1)
    (fun i => (smooth35SuccessorEndpoint_spec p hmono hp i).2.1)
    (fun i => (smooth35SuccessorEndpoint_spec p hmono hp i).2.2)

/-- The concrete summable-diagonal replacement has exactly the original algebraic
span. The backward substitution terminates inside each finite smooth-scale cluster;
it does not invoke an infinite-series convergence assumption. -/
theorem smooth35SuccessorRepair_span_eq (p : ℕ → ℕ)
    (hmono : StrictMono p) (hp : ∀ i, 0 < p i) :
    Submodule.span ℝ (Set.range (smooth35SuccessorRepair p)) =
      Submodule.span ℝ (Set.range
        (fun i => arithmeticRepair 2 (p i) (leastSmooth35Above (p i)))) := by
  classical
  let old : ℕ → ℕ → ℝ := fun i =>
    arithmeticRepair 2 (p i) (leastSmooth35Above (p i))
  have hterminal (i : ℕ) (hi : leastSmooth35Above (p i) ≤ p (i + 1)) :
      smooth35SuccessorRepair p i = old i :=
    smooth35SuccessorRepair_terminal p i hi
  have hinterior (i : ℕ) (hi : p (i + 1) < leastSmooth35Above (p i)) :
      smooth35SuccessorRepair p i = old i -
        ((p (i + 1) : ℝ) / (p i : ℝ)) • old (i + 1) := by
    funext k
    exact smooth35SuccessorRepair_interior p hmono hp i k hi
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨i, rfl⟩
    by_cases hi : leastSmooth35Above (p i) ≤ p (i + 1)
    · rw [hterminal i hi]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [hinterior i (by omega)]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨i, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i + 1, rfl⟩))
  · have hmem (m : ℕ) : ∀ i,
        leastSmooth35Above (p i) - p i = m →
        old i ∈ Submodule.span ℝ (Set.range (smooth35SuccessorRepair p)) := by
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro i hmi
        by_cases hi : leastSmooth35Above (p i) ≤ p (i + 1)
        · rw [← hterminal i hi]
          exact Submodule.subset_span ⟨i, rfl⟩
        · have hint : p (i + 1) < leastSmooth35Above (p i) := by omega
          have hnext : p i < p (i + 1) := hmono (by omega)
          have hE := leastSmooth35Above_eq_of_between hnext.le hint
          have hdec : leastSmooth35Above (p (i + 1)) - p (i + 1) < m := by
            rw [hE]
            omega
          have hnextmem := ih _ hdec (i + 1) rfl
          have heq : old i = smooth35SuccessorRepair p i +
              ((p (i + 1) : ℝ) / (p i : ℝ)) • old (i + 1) := by
            rw [hinterior i hint]
            abel
          rw [heq]
          exact Submodule.add_mem _ (Submodule.subset_span ⟨i, rfl⟩)
            (Submodule.smul_mem _ _ hnextmem)
    apply Submodule.span_le.mpr
    rintro f ⟨i, rfl⟩
    exact hmem _ i rfl

end
end RiemannResearch.RH.Pareto
