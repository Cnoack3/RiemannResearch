import RiemannResearch.RH.ParetoProgressionDigamma

/-!
# Exact occurrence Green weights

Source: Christian Noack, user-provided signal_to_noise_RH_program (2)(1).pdf,
Section 10, equation (17). Summing the actual CRT progression weights
preserves every return and gives an exact digamma difference.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto
/-- Exact Pareto mass of consecutive CRT atoms, including every return. -/
theorem progressionWeight_block_sum (P a N : ℕ) (hP : 0 < P)
    (ha : 0 < a) (hend : a + N ≤ P) :
    (∑ j ∈ Finset.range N, progressionWeight P (a+j)) =
      1 / (P : ℝ) *
        ((Complex.digamma ((((a+N : ℕ) : ℝ) / P : ℝ) : ℂ)).re -
         (Complex.digamma (((a : ℝ) / P : ℝ) : ℂ)).re) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev : a + N ≤ P := by omega
    rw [Finset.sum_range_succ, ih hprev,
      progressionWeight_eq_digamma P (a+N) hP (by omega) (by omega)]
    push_cast
    ring

/-- The occurrence Green tail is an exact digamma difference. -/
theorem progressionWeight_green_tail (P a : ℕ) (hP : 0 < P)
    (ha : 0 < a) (haP : a ≤ P) :
    (∑ j ∈ Finset.range (P-a), progressionWeight P (a+j)) =
      1 / (P : ℝ) *
        ((Complex.digamma 1).re -
         (Complex.digamma (((a : ℝ) / P : ℝ) : ℂ)).re) := by
  rw [progressionWeight_block_sum P a (P-a) hP ha (by omega),
    Nat.add_sub_of_le haP]
  have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hP)
  simp [hPr]

/-- The complete finite Green kernel in the occurrence coordinates. -/
def occurrenceGreen (P n m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (P - max n m), progressionWeight P (max n m + j)

theorem occurrenceGreen_eq_digamma (P n m : ℕ) (hP : 0 < P)
    (hn : 0 < n) (hnP : n ≤ P) (hmP : m ≤ P) :
    occurrenceGreen P n m = 1 / (P : ℝ) *
      ((Complex.digamma 1).re -
        (Complex.digamma (((((max n m : ℕ) : ℝ) / (P : ℝ)) : ℝ) : ℂ)).re) := by
  exact progressionWeight_green_tail P (max n m) hP
    (lt_of_lt_of_le hn (le_max_left n m)) (max_le hnP hmP)

theorem occurrenceGreen_symmetric (P n m : ℕ) :
    occurrenceGreen P n m = occurrenceGreen P m n := by
  simp only [occurrenceGreen, max_comm]

end RiemannResearch.RH.Pareto
