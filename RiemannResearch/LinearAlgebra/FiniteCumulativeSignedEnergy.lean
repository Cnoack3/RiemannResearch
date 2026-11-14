import RiemannResearch.LinearAlgebra.FiniteCumulativeCellEnergy
import RiemannResearch.Analysis.CumulativeEnergySummability
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact signed cumulative energy

Source: user-provided `Reciprocal_Residue_Density_and_Direct_RH_Agenda (1).tex`,
Section 7. These finite identities preserve every signed cross term. The
arithmetic application is the actual Mobius vector, not an arbitrary minimizer.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.CumulativeCellEnergy

/-- The finite suffix weight. Only indices at most `N` are used as Gram entries. -/
def tailWeight (w : ℕ → ℝ) (N i : ℕ) : ℝ := cumulative w N - cumulative w i

theorem tailWeight_self (w : ℕ → ℝ) (N : ℕ) : tailWeight w N N = 0 := by
  simp [tailWeight]

theorem tailWeight_difference (w : ℕ → ℝ) (N i : ℕ) :
    tailWeight w N i - tailWeight w N (i + 1) = w i := by
  simp only [tailWeight, cumulative, Finset.sum_range_succ]
  ring

theorem tailWeight_succ (w : ℕ → ℝ) (N i : ℕ) :
    tailWeight w (N + 1) i = tailWeight w N i + w N := by
  simp only [tailWeight, cumulative, Finset.sum_range_succ]
  ring

theorem tailWeight_nonneg (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (N i : ℕ) (hi : i ≤ N) : 0 ≤ tailWeight w N i := by
  apply sub_nonneg.mpr
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
    (fun n _ _ => hw n)

theorem tailWeight_eq_sum_ite (w : ℕ → ℝ) (N i : ℕ) (hi : i ≤ N) :
    tailWeight w N i = ∑ n ∈ Finset.range N, if i ≤ n then w n else 0 := by
  have hfilter : (Finset.range N).filter (fun n => n < i) = Finset.range i := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hhead : (∑ n ∈ Finset.range N, if n < i then w n else 0) =
      cumulative w i := by
    rw [← Finset.sum_filter, hfilter]
    rfl
  have hsplit : cumulative w N = cumulative w i +
      ∑ n ∈ Finset.range N, if i ≤ n then w n else 0 := by
    rw [← hhead, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hni : n < i
    · simp [hni, Nat.not_le.mpr hni]
    · simp [hni, Nat.le_of_not_gt hni]
  unfold tailWeight
  linarith

/-- Finite interchange of cumulative and suffix sums, with no convergence input. -/
theorem weighted_cumulative_eq_sum_tail (w b : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, w n * cumulative b (n + 1)) =
      ∑ i ∈ Finset.range N, b i * tailWeight w N i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp_rw [tailWeight_succ]
    rw [tailWeight_self]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [cumulative, Finset.sum_range_succ]
    ring

/-- Diagonal part of the cumulative Gram quadratic form. -/
def diagonalEnergy (w a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, a i ^ 2 * tailWeight w N i

/-- The signed upper triangle, including its factor of two. -/
def offDiagonalEnergy (w a : ℕ → ℝ) (N : ℕ) : ℝ :=
  2 * ∑ j ∈ Finset.range N, a j * cumulative a j * tailWeight w N j

theorem diagonalEnergy_eq_weighted_square_prefix (w a : ℕ → ℝ) (N : ℕ) :
    diagonalEnergy w a N =
      ∑ n ∈ Finset.range N, w n * cumulative (fun i => a i ^ 2) (n + 1) :=
  (weighted_cumulative_eq_sum_tail w (fun i => a i ^ 2) N).symm

/-- Exact finite decomposition; the cross term is signed, never absolute-valued. -/
theorem weightedPrefixEnergy_eq_diagonal_add_offDiagonal (w a : ℕ → ℝ) (N : ℕ) :
    weightedPrefixEnergy w a N = diagonalEnergy w a N + offDiagonalEnergy w a N := by
  have h := weightedPrefixEnergy_signed_identity a (tailWeight w N) N
  simp only [tailWeight_difference, tailWeight_self, zero_mul, sub_zero] at h
  rw [h]
  unfold diagonalEnergy offDiagonalEnergy
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem offDiagonalEnergy_eq_pair_sum (w a : ℕ → ℝ) (N : ℕ) :
    offDiagonalEnergy w a N =
      2 * ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j,
        a i * a j * tailWeight w N j := by
  unfold offDiagonalEnergy cumulative
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem diagonalEnergy_nonneg (w a : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (N : ℕ) :
    0 ≤ diagonalEnergy w a N := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (sq_nonneg _) (tailWeight_nonneg w hw N i
    (Finset.mem_range.mp hi).le)

theorem diagonalEnergy_le_linear_weight (w a : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (ha : ∀ n, a n ^ 2 ≤ 1) (N : ℕ) :
    diagonalEnergy w a N ≤ ∑ n ∈ Finset.range N, w n * (n + 1 : ℕ) := by
  rw [diagonalEnergy_eq_weighted_square_prefix]
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_left _ (hw n)
  calc
    cumulative (fun i => a i ^ 2) (n + 1) ≤ ∑ _i ∈ Finset.range (n + 1), (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => ha i)
    _ = _ := by simp

/-- Once the diagonal is controlled, bounded energy is exactly an upper
bound for the signed off-diagonal part. -/
theorem bounded_prefixEnergy_iff_bounded_offDiagonal (w a : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (D : ℝ) (hD : ∀ N, diagonalEnergy w a N ≤ D) :
    (∃ A : ℝ, ∀ N, weightedPrefixEnergy w a N ≤ A) ↔
      ∃ B : ℝ, ∀ N, offDiagonalEnergy w a N ≤ B := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A, fun N => ?_⟩
    have he := weightedPrefixEnergy_eq_diagonal_add_offDiagonal w a N
    have hd := diagonalEnergy_nonneg w a hw N
    linarith [hA N]
  · rintro ⟨B, hB⟩
    refine ⟨D + B, fun N => ?_⟩
    rw [weightedPrefixEnergy_eq_diagonal_add_offDiagonal]
    exact add_le_add (hD N) (hB N)

theorem summable_prefixEnergy_iff_bounded_offDiagonal (w a : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (D : ℝ) (hD : ∀ N, diagonalEnergy w a N ≤ D) :
    Summable (fun n => w n * cumulative a (n + 1) ^ 2) ↔
      ∃ B : ℝ, ∀ N, offDiagonalEnergy w a N ≤ B := by
  rw [RiemannResearch.Analysis.NonnegativeEnergy.summable_iff_nonnegative_prefix_bound
    _ (fun n => mul_nonneg (hw n) (sq_nonneg _))]
  exact bounded_prefixEnergy_iff_bounded_offDiagonal w a hw D hD

/-- Exact prefix splitting at an arbitrary initial head. -/
theorem cumulative_add_shift (a : ℕ → ℝ) (N K : ℕ) :
    cumulative a (N + K) =
      cumulative a N + cumulative (fun i => a (N+i)) K := by
  exact Finset.sum_range_add a N K

/-- Complete shifted energy expansion. No positivity assumption is needed;
the head square and its signed interaction with the new block are retained. -/
theorem shifted_weightedPrefixEnergy_identity (w a : ℕ → ℝ) (N K : ℕ) :
    (∑ i ∈ Finset.range K, w i * cumulative a (N+i+1)^2) =
      cumulative a N ^ 2 * cumulative w K +
      2 * cumulative a N *
        (∑ j ∈ Finset.range K, a (N+j) * tailWeight w K j) +
      diagonalEnergy w (fun i => a (N+i)) K +
      offDiagonalEnergy w (fun i => a (N+i)) K := by
  have hs : (∑ i ∈ Finset.range K, w i * cumulative a (N+i+1)^2) =
      cumulative a N ^ 2 * cumulative w K +
      2 * cumulative a N *
        (∑ i ∈ Finset.range K, w i * cumulative (fun j => a (N+j)) (i+1)) +
      weightedPrefixEnergy w (fun j => a (N+j)) K := by
    have hp (i : ℕ) : cumulative a (N+i+1) =
        cumulative a N + cumulative (fun j => a (N+j)) (i+1) := by
      simpa only [Nat.add_assoc] using cumulative_add_shift a N (i+1)
    simp_rw [hp]
    unfold weightedPrefixEnergy
    change _ = cumulative a N ^ 2 * (∑ i ∈ Finset.range K, w i) + _ + _
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hs, weighted_cumulative_eq_sum_tail,
    weightedPrefixEnergy_eq_diagonal_add_offDiagonal]
  ring

end RiemannResearch.LinearAlgebra.CumulativeCellEnergy
