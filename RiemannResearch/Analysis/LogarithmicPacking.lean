import RiemannResearch.Analysis.FiniteRealPacking
import RiemannResearch.Analysis.LogarithmicBlockSum

/-!
# Logarithmic sums of separated points

Source: user-provided argument, §3 of
`Dyadic_Gram_Prefix_Ordinary_Proof_20260910.md`.
At each step remove a point of maximal absolute value. Interval packing gives
its rank lower bound. This realizes the ordinary sorted-distance argument
without constructing or assuming a sorting permutation.
-/

open scoped BigOperators

namespace Finset

/-- A single exceptional logarithm plus the exact finite rank majorant bounds
every nonempty finite separated family. -/
theorem sum_log_inv_abs_le_rank_sum
    {ι : Type*} (q : ℕ) (hq : 0 < q) (f : ι → ℝ) (H : ℝ)
    (s : Finset ι) (hs : s.Nonempty)
    (hpos : ∀ i ∈ s, 0 < |f i|)
    (hsmall : ∀ i ∈ s, Real.log (1 / |f i|) ≤ H)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      1 / (2 * (q : ℝ)) ≤ |f i - f j|) :
    (∑ i ∈ s, Real.log (1 / |f i|)) ≤
      H + ∑ i ∈ range (s.card - 1), Real.log (4 * q / ((i : ℝ) + 1)) := by
  classical
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  induction s using Finset.strongInductionOn
  rename_i s ih
  obtain ⟨x, hx, hmax⟩ := s.exists_max_image (fun i => |f i|) hs
  have hc : (s.erase x).card + 1 = s.card := Finset.card_erase_add_one hx
  have hcR : ((s.erase x).card : ℝ) + 1 = s.card := by exact_mod_cast hc
  have hsplit := Finset.sum_erase_add s (fun i => Real.log (1 / |f i|)) hx
  by_cases ht : (s.erase x).Nonempty
  · have hn : 1 ≤ (s.erase x).card := Finset.card_pos.mpr ht
    have hn0 : 0 < ((s.erase x).card : ℝ) := by exact_mod_cast hn
    have hrest := ih (s.erase x) (Finset.erase_ssubset hx) ht
      (fun i hi => hpos i (Finset.mem_of_mem_erase hi))
      (fun i hi => hsmall i (Finset.mem_of_mem_erase hi))
      (fun i hi j hj hne => hsep i (Finset.mem_of_mem_erase hi)
        j (Finset.mem_of_mem_erase hj) hne)
    have hpack := card_sub_one_mul_spacing_le_two_mul_radius s f
      (1 / (2 * (q : ℝ))) |f x| (by positivity) (abs_nonneg _)
      hmax hsep
    have hpack' : ((s.card : ℝ) - 1) / (2 * q) ≤ 2 * |f x| := by
      simpa [div_eq_mul_inv] using hpack
    have hrank := (div_le_iff₀ (show 0 < (2 : ℝ) * q by positivity)).mp hpack'
    have hinv : 1 / |f x| ≤ 4 * q / ((s.erase x).card : ℝ) := by
      apply (div_le_div_iff₀ (hpos x hx) hn0).mpr
      nlinarith
    have hlog := Real.log_le_log (one_div_pos.mpr (hpos x hx)) hinv
    have hpred : s.card - 1 = (s.erase x).card := by omega
    have hncast : (((s.erase x).card - 1 : ℕ) : ℝ) + 1 =
        (s.erase x).card := by
      exact_mod_cast Nat.sub_add_cancel hn
    have hsum := Finset.sum_range_succ
      (fun i : ℕ => Real.log (4 * q / ((i : ℝ) + 1))) ((s.erase x).card - 1)
    rw [Nat.sub_add_cancel hn, hncast] at hsum
    rw [hpred, hsum]
    nlinarith
  · have ht0 : s.erase x = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    have hsone : s.card = 1 := by simpa [ht0] using hc.symm
    have hsumone : (∑ i ∈ s, Real.log (1 / |f i|)) =
        Real.log (1 / |f x|) := by
      simpa [ht0] using hsplit.symm
    rw [hsone, hsumone]
    simpa using hsmall x hx

/-- The finite block estimate needed for the irrational-rotation prefix.
The absolute values are physical distances; no sorting hypothesis is required. -/
theorem sum_log_inv_abs_le_of_block_spacing
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) (q : ℕ) (hq : 0 < q)
    (hcard : s.card ≤ q) (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ i ∈ s, 0 < |f i|)
    (hsmall : ∀ i ∈ s, Real.log (1 / |f i|) ≤ C * q)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      1 / (2 * (q : ℝ)) ≤ |f i - f j|) :
    (∑ i ∈ s, Real.log (1 / |f i|)) ≤ (C + 1 + Real.log 4) * q := by
  have h4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  by_cases hs : s.Nonempty
  · have h := sum_log_inv_abs_le_rank_sum q hq f (C * q) s hs hpos hsmall hsep
    have hpad :
        (∑ i ∈ range (s.card - 1), Real.log (4 * q / ((i : ℝ) + 1))) ≤
        ∑ i ∈ range q, Real.log (4 * q / ((i : ℝ) + 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (le_trans (Nat.sub_le _ _) hcard))
      intro i hi _
      have hiq : (i : ℝ) + 1 ≤ q := by
        exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
      apply Real.log_nonneg
      apply (le_div_iff₀ (show 0 < (i : ℝ) + 1 by positivity)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) q]
    have hsum := Real.sum_log_four_nat_div_succ_le q
    nlinarith
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hs0, Finset.sum_empty]
    positivity

end Finset
