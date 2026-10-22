import RiemannResearch.NumberTheory.QuotientWindowSquareBound

/-!
# Exact separation of quotient-window square energy

The upper quotient windows are empty or singletons, so their square energy
can be reindexed without discarding cross terms. This formalizes Section 1
of `ReciprocalChargeNormLimit20260924.md` (2026-09-24).
-/

noncomputable section
open scoped BigOperators
open Filter

namespace RiemannResearch.NumberTheory.QuotientWindow

/-- Every positive integer at most `N` lies in its quotient window. -/
theorem mem_window_quotient {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    n ∈ window N (N / n) := by
  have hq : 0 < N / n := by
    have h : 1 ≤ N / n := (Nat.le_div_iff_mul_le hn).mpr (by simpa using hnN)
    omega
  have hlo : (N / n) * n ≤ N := Nat.div_mul_le_self N n
  have hhi : N < (N / n + 1) * n :=
    (Nat.div_lt_iff_lt_mul hn).mp (Nat.lt_succ_self (N / n))
  apply Finset.mem_Ioc.mpr
  exact ⟨(Nat.div_lt_iff_lt_mul (by omega : 0 < N / n + 1)).mpr
      (by simpa [Nat.mul_comm] using hhi),
    (Nat.le_div_iff_mul_le hq).mpr (by simpa [Nat.mul_comm] using hlo)⟩

/-- Above the diagonal, squaring the window sum creates no cross terms. -/
theorem window_sum_sq_eq_sum_sq (η : ℕ → ℝ) {N d : ℕ}
    (hd : 0 < d) (hN : N < d * (d + 1)) :
    (∑ n ∈ window N d, η n) ^ 2 = ∑ n ∈ window N d, (η n) ^ 2 := by
  have hsub := window_subsingleton hd hN
  by_cases he : (window N d).Nonempty
  · obtain ⟨n, hn⟩ := he
    have hw : window N d = {n} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hn, fun m hm => hsub hm hn⟩
    simp [hw]
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

/-- The union of the upper windows is exactly the isolated arithmetic set. -/
theorem upper_windows_biUnion (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun d => N < d * (d + 1))).biUnion (window N) =
      (Finset.Icc 1 N).filter (fun n => N < (N / n) * (N / n + 1)) := by
  ext n
  constructor
  · intro hn
    obtain ⟨d, hd, hnd⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hdI, hdN⟩ := Finset.mem_filter.mp hd
    have hd0 : 0 < d := (Finset.mem_Icc.mp hdI).1
    refine Finset.mem_filter.mpr ⟨window_subset hd0 hnd, ?_⟩
    simpa only [quotient_of_mem_window hd0 hnd] using hdN
  · intro hn
    obtain ⟨hnI, hnN⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn0, hnle⟩ := Finset.mem_Icc.mp hnI
    have hq0 : 1 ≤ N / n :=
      (Nat.le_div_iff_mul_le hn0).mpr (by simpa using hnle)
    apply Finset.mem_biUnion.mpr
    refine ⟨N / n, Finset.mem_filter.mpr ⟨?_, hnN⟩,
      mem_window_quotient hn0 hnle⟩
    exact Finset.mem_Icc.mpr ⟨hq0, Nat.div_le_self N n⟩

/-- Exact reindexing of the upper-window square energy. -/
theorem sum_upper_window_sq (η : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ (Finset.Icc 1 N).filter (fun d => N < d * (d + 1)),
      (∑ n ∈ window N d, η n) ^ 2) =
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => N < (N / n) * (N / n + 1)),
      (η n) ^ 2 := by
  have hdisj : Set.PairwiseDisjoint
      (↑((Finset.Icc 1 N).filter (fun d => N < d * (d + 1))) : Set ℕ)
      (window N) := by
    intro d hd e he hde
    exact pairwise_disjoint N (Finset.mem_filter.mp hd).1
      (Finset.mem_filter.mp he).1 hde
  calc
    _ = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => N < d * (d + 1)),
        ∑ n ∈ window N d, (η n) ^ 2 := by
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨hdI, hdN⟩ := Finset.mem_filter.mp hd
      exact window_sum_sq_eq_sum_sq η (Finset.mem_Icc.mp hdI).1 hdN
    _ = ∑ n ∈ ((Finset.Icc 1 N).filter (fun d => N < d * (d + 1))).biUnion
        (window N), (η n) ^ 2 := by
      rw [Finset.sum_biUnion hdisj]
    _ = _ := by rw [upper_windows_biUnion]

/-- The exact lower-window and isolated-window energy decomposition. -/
theorem sum_window_sq_eq_low_add_isolated (η : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, (∑ n ∈ window N d, η n) ^ 2) =
      (∑ d ∈ (Finset.Icc 1 N).filter (fun d => d * (d + 1) ≤ N),
        (∑ n ∈ window N d, η n) ^ 2) +
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => N < (N / n) * (N / n + 1)),
        (η n) ^ 2 := by
  have hsplit :
      (∑ d ∈ Finset.Icc 1 N, (∑ n ∈ window N d, η n) ^ 2) =
        (∑ d ∈ (Finset.Icc 1 N).filter (fun d => d * (d + 1) ≤ N),
          (∑ n ∈ window N d, η n) ^ 2) +
        ∑ d ∈ (Finset.Icc 1 N).filter (fun d => N < d * (d + 1)),
          (∑ n ∈ window N d, η n) ^ 2 := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : d * (d + 1) ≤ N
    · simp [h, not_lt_of_ge h]
    · simp [h, Nat.lt_of_not_ge h]
  rw [hsplit, sum_upper_window_sq]

/-- Every fixed positive integer enters the isolated set by cutoff `n²`. -/
theorem quotient_diagonal_of_square_le {N n : ℕ} (hn : 0 < n) (hN : n ^ 2 ≤ N) :
    n ∈ (Finset.Icc 1 N).filter (fun n => N < (N / n) * (N / n + 1)) := by
  have hnN : n ≤ N := by nlinarith
  have hnq : n ≤ N / n := (Nat.le_div_iff_mul_le hn).mpr (by simpa [pow_two] using hN)
  have hhi : N < (N / n + 1) * n :=
    (Nat.div_lt_iff_lt_mul hn).mp (Nat.lt_succ_self (N / n))
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn, hnN⟩, ?_⟩
  calc
    N < (N / n + 1) * n := hhi
    _ ≤ (N / n + 1) * (N / n) := Nat.mul_le_mul_left _ hnq
    _ = (N / n) * (N / n + 1) := Nat.mul_comm _ _

theorem quotient_diagonal_eventually {n : ℕ} (hn : 0 < n) :
    ∀ᶠ N : ℕ in atTop,
      n ∈ (Finset.Icc 1 N).filter (fun n => N < (N / n) * (N / n + 1)) := by
  filter_upwards [eventually_ge_atTop (n ^ 2)] with N hN
  exact quotient_diagonal_of_square_le hn hN

end RiemannResearch.NumberTheory.QuotientWindow
