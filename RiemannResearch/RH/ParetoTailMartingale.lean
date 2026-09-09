import RiemannResearch.RH.ParetoPacketCoordinates

/-!
# Exact Pareto tail-martingale identities and the mean-zero obstruction

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Sections 6–7, and the preceding discussion of the Brownian analogy.
The vectors are concrete actual-Hilbert-space random variables. The finite
distribution, means and covariances are proved here; a bundled filtration is
not needed for these identities.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

def paretoTailMartingale (N : ℕ) : ThresholdHilbert :=
  ∑ n ∈ Finset.range N, tailBasisHilbert n

theorem paretoTailMartingale_succ (N : ℕ) :
    paretoTailMartingale (N + 1) = paretoTailMartingale N + tailBasisHilbert N := by
  simp [paretoTailMartingale, Finset.sum_range_succ]

theorem paretoTailMartingale_mean (N : ℕ) :
    inner ℝ (paretoTailMartingale N) hilbertOne = 0 := by
  simp [paretoTailMartingale, sum_inner, tailBasis_inner_one]

theorem paretoTailMartingale_inner_basis (N m : ℕ) :
    inner ℝ (paretoTailMartingale N) (tailBasisHilbert m) =
      if m < N then 1 else 0 := by
  simp [paretoTailMartingale, sum_inner, tailBasis_inner]

theorem paretoTailMartingale_inner_of_le (N M : ℕ) (hMN : M ≤ N) :
    inner ℝ (paretoTailMartingale N) (paretoTailMartingale M) = (M : ℝ) := by
  conv_lhs => rhs; unfold paretoTailMartingale
  rw [inner_sum]
  calc
    (∑ m ∈ Finset.range M, inner ℝ (paretoTailMartingale N) (tailBasisHilbert m)) =
        ∑ _m ∈ Finset.range M, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [paretoTailMartingale_inner_basis, if_pos
        (lt_of_lt_of_le (Finset.mem_range.mp hm) hMN)]
    _ = (M : ℝ) := by simp

/-- Brownian integer-time covariance holds, without Gaussian independence. -/
theorem paretoTailMartingale_covariance (N M : ℕ) :
    inner ℝ (paretoTailMartingale N) (paretoTailMartingale M) = (min N M : ℕ) := by
  rcases le_total N M with h | h
  · rw [real_inner_comm, paretoTailMartingale_inner_of_le M N h, min_eq_left h]
  · rw [paretoTailMartingale_inner_of_le N M h, min_eq_right h]

theorem paretoTailMartingale_norm_sq (N : ℕ) :
    ‖paretoTailMartingale N‖ ^ 2 = (N : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, paretoTailMartingale_covariance, min_self]

/-- The complete two-value distribution: one on the revealed head, minus N
on the remaining tail. No infinite-tail truncation occurs. -/
theorem paretoTailMartingale_physical (N k : ℕ) :
    hilbertGibbsPhysical (paretoTailMartingale N) k =
      if k < N then 1 else -(N : ℝ) := by
  induction N with
  | zero => simp [paretoTailMartingale, hilbertGibbsPhysical]
  | succ N ih =>
      rw [paretoTailMartingale_succ, hilbertGibbsPhysical_add]
      change hilbertGibbsPhysical (paretoTailMartingale N) k +
        hilbertGibbsPhysical (tailBasisHilbert N) k = _
      rw [ih, hilbertGibbsPhysical_tailBasis]
      by_cases hlt : k < N
      · have hne : k ≠ N := by omega
        have hnot : ¬N < k := by omega
        have hlt' : k < N + 1 := by omega
        simp [tailBasisPhysical, hlt, hne, hnot, hlt']
      · by_cases he : k = N
        · subst k
          simp [tailBasisPhysical]
        · have hgt : N < k := by omega
          have hnot : ¬k < N + 1 := by omega
          simp [tailBasisPhysical, hlt, he, hgt, hnot]
          ring

theorem paretoTailMartingale_error_sq (N : ℕ) :
    ‖paretoTailMartingale N - hilbertOne‖ ^ 2 = (N : ℝ) + 1 := by
  have h := LinearAlgebra.norm_add_smul_sq_exact
    (paretoTailMartingale N) hilbertOne (-1)
  simp only [neg_one_smul, ← sub_eq_add_neg, paretoTailMartingale_norm_sq,
    paretoTailMartingale_mean, hilbertOne_norm_sq] at h
  linarith

/-- Every mean-zero exact-head vector has the same first N Haar coefficients. -/
theorem mean_zero_exact_head_tail_coefficient (F : ThresholdHilbert) (N j : ℕ)
    (hmean : inner ℝ F hilbertOne = 0)
    (hhead : ∀ k < N, hilbertGibbsPhysical F k = 1) (hj : j < N) :
    inner ℝ F (tailBasisHilbert j) = 1 := by
  rw [tailBasis_coefficient_of_mean_zero F j hmean, hhead j hj]
  have hs : (∑ k ∈ Finset.range j, paretoWeight k * hilbertGibbsPhysical F k) =
      ∑ k ∈ Finset.range j, paretoWeight k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hhead k (lt_trans (Finset.mem_range.mp hk) hj), mul_one]
  rw [hs, paretoWeight_partial_sum]
  ring

/-- Exact Pythagorean obstruction: every mean-zero exact-head vector pays N,
plus the full norm of its remaining orthogonal defect. -/
theorem mean_zero_exact_head_energy (F : ThresholdHilbert) (N : ℕ)
    (hmean : inner ℝ F hilbertOne = 0)
    (hhead : ∀ k < N, hilbertGibbsPhysical F k = 1) :
    ‖F‖ ^ 2 = (N : ℝ) + ‖F - paretoTailMartingale N‖ ^ 2 := by
  have hi : inner ℝ F (paretoTailMartingale N) = (N : ℝ) := by
    unfold paretoTailMartingale
    rw [inner_sum]
    calc
      (∑ j ∈ Finset.range N, inner ℝ F (tailBasisHilbert j)) =
          ∑ _j ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact mean_zero_exact_head_tail_coefficient F N j hmean hhead
          (Finset.mem_range.mp hj)
      _ = (N : ℝ) := by simp
  have he := LinearAlgebra.norm_add_smul_sq_exact F (paretoTailMartingale N) (-1)
  simp only [neg_one_smul, ← sub_eq_add_neg, paretoTailMartingale_norm_sq, hi] at he
  linarith

theorem mean_zero_exact_head_norm_lower (F : ThresholdHilbert) (N : ℕ)
    (hmean : inner ℝ F hilbertOne = 0)
    (hhead : ∀ k < N, hilbertGibbsPhysical F k = 1) :
    (N : ℝ) ≤ ‖F‖ ^ 2 := by
  rw [mean_zero_exact_head_energy F N hmean hhead]
  exact le_add_of_nonneg_right (sq_nonneg _)

end
end RiemannResearch.RH.Pareto
