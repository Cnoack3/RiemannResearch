import RiemannResearch.RH.ThresholdNormalizedTail
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Square-summable weighted tails of dyadic adjoint fixed vectors

Source: independently developed from the argument in
`RH_Iff_Two_Seed_Approximation_20260914.md`, Section 3.

Dyadic fixedness replaces the general Hardy estimate: the fixed equation turns
each infinite tail into twice one finite block. The resulting positive kernel
has column sums at most four. Thus all signed arithmetic information remains
in the exact tail before the Cauchy--Schwarz estimate is applied.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis
noncomputable section

private theorem dyadicTailKernelColumn_le (s : Finset ℕ) (k : ℕ) :
    (∑ n ∈ s, if n ≤ k ∧ k < 2*n then (2 : ℝ) / n else 0) ≤ 4 := by
  classical
  by_cases hk : k = 0
  · subst k
    have hz : ∀ n : ℕ, ¬ (n ≤ 0 ∧ 0 < 2*n) := by
      intro n hn
      omega
    have he : (∑ n ∈ s, if n ≤ 0 ∧ 0 < 2*n then (2 : ℝ) / n else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      exact if_neg (hz n)
    rw [he]
    norm_num
  · have hkp : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    let t := s.filter (fun n => n ≤ k ∧ k < 2*n)
    have hsub : t ⊆ Finset.Icc 1 k := by
      intro n hn
      have hc := (Finset.mem_filter.mp hn).2
      simp only [Finset.mem_Icc]
      omega
    have hcard : (t.card : ℝ) ≤ k := by
      have hc := Finset.card_le_card hsub
      simpa using (show (t.card : ℝ) ≤ ((Finset.Icc 1 k).card : ℝ) by
        exact_mod_cast hc)
    calc
      _ = ∑ n ∈ t, (2 : ℝ) / n := by simp [t, Finset.sum_filter]
      _ ≤ ∑ _n ∈ t, (4 : ℝ) / k := by
        apply Finset.sum_le_sum
        intro n hn
        have hc := (Finset.mem_filter.mp hn).2
        have hnp : (0 : ℝ) < n := by
          exact_mod_cast (show 0 < n by omega)
        apply (div_le_div_iff₀ hnp hkp).2
        have hkn : (k : ℝ) < 2*(n : ℝ) := by exact_mod_cast hc.2
        linarith
      _ = (t.card : ℝ) * (4 / k) := by simp [nsmul_eq_mul]
      _ ≤ (k : ℝ) * (4 / k) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 4 := by field_simp

/-- A positive dyadic-block kernel with the displayed row bound sends a
summable energy sequence to a square-summable tail sequence. -/
theorem square_summable_of_dyadic_block_bound
    (T q : ℕ → ℝ) (hq : Summable q) (hq0 : ∀ k, 0 ≤ q k)
    (hT : ∀ n : ℕ, 0 < n →
      T n ^ 2 ≤ (2 : ℝ) / n * ∑ k ∈ Finset.Ico n (2*n), q k) :
    Summable (fun n => T n ^ 2) := by
  classical
  have hbound (N : ℕ) :
      (∑ n ∈ Finset.Ico 1 N, T n ^ 2) ≤ 4 * ∑' k, q k := by
    calc
      _ ≤ ∑ n ∈ Finset.Ico 1 N,
          (2 : ℝ) / n * ∑ k ∈ Finset.Ico n (2*n), q k := by
        apply Finset.sum_le_sum
        intro n hn
        exact hT n (by have := (Finset.mem_Ico.mp hn).1; omega)
      _ = ∑ n ∈ Finset.Ico 1 N, ∑ k ∈ Finset.range (2*N),
          if n ≤ k ∧ k < 2*n then (2 : ℝ) / n * q k else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnN := (Finset.mem_Ico.mp hn).2
        have hs : (Finset.range (2*N)).filter (fun k => n ≤ k ∧ k < 2*n) =
            Finset.Ico n (2*n) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
          omega
        rw [← Finset.sum_filter, hs, Finset.mul_sum]
      _ = ∑ k ∈ Finset.range (2*N), q k *
          ∑ n ∈ Finset.Ico 1 N,
            if n ≤ k ∧ k < 2*n then (2 : ℝ) / n else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        split_ifs <;> ring
      _ ≤ ∑ k ∈ Finset.range (2*N), q k * 4 := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (dyadicTailKernelColumn_le (Finset.Ico 1 N) k) (hq0 k)
      _ = 4 * ∑ k ∈ Finset.range (2*N), q k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ 4 * ∑' k, q k := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact hq.sum_le_tsum _ (fun k _ => hq0 k)
  apply (summable_nat_add_iff 1).mp
  apply summable_of_sum_range_le (fun n => sq_nonneg _) (c := 4 * ∑' k, q k)
  intro N
  have hb := hbound (N+1)
  rw [Finset.sum_Ico_eq_sum_range] at hb
  simpa [Nat.add_comm] using hb

end
end RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
noncomputable section

theorem hilbertWeightedTail_sq_le_dyadic_block
    (f : ThresholdHilbert)
    (hfix : hilbertDilationAdjoint 2 (by decide) f = f)
    (n : ℕ) (hn : 0 < n) :
    hilbertWeightedTail f n ^ 2 ≤ (2 : ℝ) / n *
      ∑ k ∈ Finset.Ico n (2*n), positiveWeight k * hilbertSequence f k ^ 2 := by
  have hscale := hilbertTail_inner_scaling f 2 n (by decide) hn hfix
  rw [← hilbertWeightedTail_eq_inner f (2*n) (by omega),
    ← hilbertWeightedTail_eq_inner f n hn] at hscale
  norm_num at hscale
  have hcs := hilbertTail_inner_sub_sq_le f n (2*n) hn (by omega)
  rw [← hilbertWeightedTail_eq_inner f n hn,
    ← hilbertWeightedTail_eq_inner f (2*n) (by omega)] at hcs
  push_cast at hcs
  have hsq : (hilbertWeightedTail f n - hilbertWeightedTail f (2*n))^2 =
      hilbertWeightedTail f n ^ 2 / 4 := by
    have he : hilbertWeightedTail f (2*n) = hilbertWeightedTail f n / 2 := by
      linarith
    rw [he]
    ring
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hrec : 1 / (n : ℝ) - 1 / (2 * (n : ℝ)) = 1 / (2 * (n : ℝ)) := by
    field_simp
    ring
  rw [hsq, hrec] at hcs
  have hs := mul_le_mul_of_nonneg_left hcs (by norm_num : (0 : ℝ) ≤ 4)
  have hcoef : (4 : ℝ) * (1 / (2 * (n : ℝ))) = 2 / (n : ℝ) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num <;> ring
  calc
    hilbertWeightedTail f n ^ 2 = 4 * (hilbertWeightedTail f n ^ 2 / 4) := by ring
    _ ≤ _ := hs
    _ = (2 : ℝ) / n *
        ∑ k ∈ Finset.Ico n (2*n), positiveWeight k * hilbertSequence f k ^ 2 := by
      rw [← mul_assoc, hcoef]

/-- Actual summability provider. Its only hypothesis is genuine dyadic
adjoint fixedness in the existing complete Pareto Hilbert space. -/
theorem hilbertWeightedTail_square_summable_of_dyadic_fixed
    (f : ThresholdHilbert)
    (hfix : hilbertDilationAdjoint 2 (by decide) f = f) :
    Summable (fun n => hilbertWeightedTail f n ^ 2) :=
  RiemannResearch.Analysis.square_summable_of_dyadic_block_bound (hilbertWeightedTail f)
    (fun k => positiveWeight k * hilbertSequence f k ^ 2)
    (hilbertSequence_square_summable f)
    (fun k => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
    (hilbertWeightedTail_sq_le_dyadic_block f hfix)

theorem hilbertNormalizedTail_increment_square_summable_of_dyadic_fixed
    (f : ThresholdHilbert)
    (hfix : hilbertDilationAdjoint 2 (by decide) f = f) :
    Summable (fun n => (hilbertNormalizedTail f (n+1) -
      hilbertNormalizedTail f n)^2) :=
  hilbertNormalizedTail_increment_square_summable f
    (hilbertWeightedTail_square_summable_of_dyadic_fixed f hfix)

end
end RiemannResearch.RH.Pareto
