import RiemannResearch.Probability.DeterminantalCardinality

/-!
# Full-configuration probabilities for fixed-cardinality DPPs

Source: the user-provided projection DPP construction. The proof converts
finite inclusion probabilities into exact-configuration probabilities using
the proved almost-sure particle count. No conditional lift law is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace RiemannResearch.Probability.DPP

theorem finset_card_le_setCount {α : Type*} (A : Finset α) (s : Set α)
    (hA : ∀ i ∈ A, i ∈ s) : (A.card : ℝ≥0∞) ≤ setCount s := by
  calc
    (A.card : ℝ≥0∞) = ∑ i ∈ A, (1 : ℝ≥0∞) := by simp
    _ = ∑ i ∈ A, s.indicator (1 : α → ℝ≥0∞) i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Set.indicator_apply, hA i hi]
    _ ≤ ∑' i, s.indicator (1 : α → ℝ≥0∞) i := ENNReal.sum_le_tsum A

/-- Inclusion of N distinct sites saturates any set of cardinality at most N. -/
theorem set_eq_range_of_setCount_le {α : Type*} (N : ℕ) (e : Fin N ↪ α) (s : Set α)
    (hsub : ∀ i, e i ∈ s) (hc : setCount s ≤ N) : s = Set.range e := by
  let A : Finset α := Finset.univ.map e
  have hA : ∀ i ∈ A, i ∈ s := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact hsub j
  apply Set.Subset.antisymm
  · intro i hi
    by_contra hin
    have hiA : i ∉ A := by
      intro hm
      obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hm
      exact hin ⟨j, hji⟩
    have hb : ((insert i A).card : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
      apply (finset_card_le_setCount (insert i A) s ?_).trans hc
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hi
      · exact hA k hk
    have hcard : (insert i A).card = N + 1 := by
      simp [Finset.card_insert_of_notMem hiA, A]
    rw [hcard] at hb
    have hbad : N + 1 ≤ N := by exact_mod_cast hb
    omega
  · rintro i ⟨j, rfl⟩
    exact hsub j

variable {Ω α : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → Set α} {K : α → α → ℝ}

/-- For a DPP with exactly N points, every N-site correlation is an exact
configuration probability, not merely an inclusion probability. -/
theorem IsDPP.full_configuration_of_setCount (h : IsDPP μ X K) (N : ℕ)
    (hc : ∀ᵐ ω ∂μ, setCount (X ω) = N) (e : Fin N ↪ α) :
    μ.real {ω | X ω = Set.range e} =
      Matrix.det (Matrix.of (fun i j => K (e i) (e j))) := by
  calc
    _ = μ.real {ω | ∀ i, e i ∈ X ω} := by
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [hc] with ω hω
      apply propext
      constructor
      · intro he i
        rw [he]
        exact ⟨i, rfl⟩
      · intro he
        exact set_eq_range_of_setCount_le N e (X ω) he hω.le
    _ = _ := h.correlation N e

end RiemannResearch.Probability.DPP
