import RiemannResearch.RH.ReciprocalInfiniteCertificate

/-!
# An improved conductor-five complete reciprocal certificate

Source: independently developed exact signed recovery rows, 9 October 2026.
Orthogonality to the additional conductor-five atom allows adding the zero
charge of `(k % 3) - (k % 5)` to both head-recovery rows. This module verifies
the resulting rational 34-site certificate and the entire infinite-tail
estimate. The actual optimizer specialization is proved in
`ZetaTwoConductorFiveBound`.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ReciprocalConductorFiveCertificate
open ReciprocalInfiniteCertificate

def weightOneFive (k : ℕ) : ℝ :=
  (-5 * ((k % 2 : ℕ) : ℝ) - ((k % 3 : ℕ) : ℝ) + ((k % 5 : ℕ) : ℝ)) / 5

def weightTwoFive (k : ℕ) : ℝ :=
  2 * ((k % 2 : ℕ) : ℝ) - ((k % 3 : ℕ) : ℝ) - ((k % 5 : ℕ) : ℝ)

set_option maxRecDepth 4096 in
theorem normalized_head11_le :
    (5 / 8 : ℝ) * finiteGram (3 / 8) weightOneFive weightOneFive ≤ 39 / 50 := by
  norm_num [finiteGram, gap, weightOneFive, Fin.sum_univ_succ]

set_option maxRecDepth 4096 in
theorem normalized_head22_le :
    (1 / 32 : ℝ) * finiteGram (3 / 8) weightTwoFive weightTwoFive ≤ 59 / 100 := by
  norm_num [finiteGram, gap, weightTwoFive, Fin.sum_univ_succ]

set_option maxRecDepth 4096 in
theorem normalized_head12_sq_le :
    (5 / 256 : ℝ) * (finiteGram (3 / 8) weightOneFive weightTwoFive) ^ 2 ≤ 41 / 10000 := by
  norm_num [finiteGram, gap, weightOneFive, weightTwoFive, Fin.sum_univ_succ]

/-- All thirty residue channels occur; no prime-independence input is used. -/
theorem traceNumerator_le (a b c : ℕ) (ha : a ≤ 1) (hb : b ≤ 2) (hc : c ≤ 4) :
    (5 / 8 : ℝ) * ((-5 * (a : ℝ) - (b : ℝ) + (c : ℝ)) / 5) ^ 2 +
      (1 / 32 : ℝ) * (2 * (a : ℝ) - (b : ℝ) - (c : ℝ)) ^ 2 ≤ 49 / 40 := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num

theorem full_tail_trace_constant :
    (49 / 40 : ℝ) / (36 * (3 / 8 - 1 / 37)) = 1813 / 18540 := by norm_num

/-- The complete signed cross term is retained before Young's inequality. -/
theorem headTail_quadratic_le (A B c tail x y : ℝ)
    (hA : A ≤ 39 / 50) (hB : B ≤ 59 / 100) (hc : c ^ 2 ≤ 41 / 10000)
    (htail : tail ≤ (1813 / 18540 : ℝ) * (x ^ 2 + y ^ 2)) :
    A * x ^ 2 + 2 * c * x * y + B * y ^ 2 + tail ≤
      (3329 / 3708 : ℝ) * (x ^ 2 + y ^ 2) := by
  have hAx := mul_le_mul_of_nonneg_right hA (sq_nonneg x)
  have hBy := mul_le_mul_of_nonneg_right hB (sq_nonneg y)
  have hcy := mul_le_mul_of_nonneg_right hc (sq_nonneg y)
  have hcross : 2 * c * x * y ≤ (1 / 50 : ℝ) * x ^ 2 + (41 / 200 : ℝ) * y ^ 2 := by
    nlinarith [sq_nonneg ((1 / 50 : ℝ) * x - c * y)]
  nlinarith [sq_nonneg y]

theorem headTail_coefficient_lt_one : (3329 / 3708 : ℝ) < 1 := by norm_num

theorem secondMoment_cap : (3 / 8 : ℝ) ^ 2 = 9 / 64 := by norm_num

def fiveCharge (x y : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (5 / 8 : ℝ) * weightOneFive k * x +
    Real.sqrt (1 / 32 : ℝ) * weightTwoFive k * y

def fiveGramTerm (x y : ℝ) (k : ℕ) : ℝ :=
  (fiveCharge x y k) ^ 2 / ((k : ℝ) ^ 2 * gap (3 / 8) k)

theorem fiveCharge_sq_le (x y : ℝ) (k : ℕ) :
    (fiveCharge x y k) ^ 2 ≤ (49 / 40 : ℝ) * (x ^ 2 + y ^ 2) := by
  have hs1 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 8)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 32)
  have htrace := traceNumerator_le (k % 2) (k % 3) (k % 5)
    (by omega) (by omega) (by omega)
  change (5 / 8 : ℝ) * (weightOneFive k) ^ 2 +
    (1 / 32 : ℝ) * (weightTwoFive k) ^ 2 ≤ 49 / 40 at htrace
  have htr := mul_le_mul_of_nonneg_right htrace (add_nonneg (sq_nonneg x) (sq_nonneg y))
  have he : (fiveCharge x y k) ^ 2 +
      (Real.sqrt (5 / 8 : ℝ) * weightOneFive k * y -
        Real.sqrt (1 / 32 : ℝ) * weightTwoFive k * x) ^ 2 =
      ((5 / 8 : ℝ) * (weightOneFive k) ^ 2 +
        (1 / 32 : ℝ) * (weightTwoFive k) ^ 2) * (x ^ 2 + y ^ 2) := by
    unfold fiveCharge
    simp only [add_sq, sub_sq, mul_pow, hs1, hs2]
    ring
  linarith [sq_nonneg (Real.sqrt (5 / 8 : ℝ) * weightOneFive k * y -
    Real.sqrt (1 / 32 : ℝ) * weightTwoFive k * x)]

theorem fiveGramTerm_le (x y : ℝ) (K k : ℕ) (hK : 3 ≤ K) (hk : K ≤ k) :
    fiveGramTerm x y k ≤
      ((49 / 40 : ℝ) * (x ^ 2 + y ^ 2) / gap (3 / 8) K) / (k : ℝ) ^ 2 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hg := gap_pos (3 / 8) (by norm_num) k (hK.trans hk)
  have hgK := gap_pos (3 / 8) (by norm_num) K hK
  have hmon := gap_lower (3 / 8) K k (by omega) hk
  unfold fiveGramTerm
  calc
    _ ≤ ((49 / 40 : ℝ) * (x ^ 2 + y ^ 2)) / ((k : ℝ) ^ 2 * gap (3 / 8) k) :=
      div_le_div_of_nonneg_right (fiveCharge_sq_le x y k) (by positivity)
    _ ≤ ((49 / 40 : ℝ) * (x ^ 2 + y ^ 2)) / ((k : ℝ) ^ 2 * gap (3 / 8) K) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hmon (sq_nonneg _)
    _ = _ := by ring

theorem fiveGram_summable (x y : ℝ) :
    Summable (fun i : ℕ => fiveGramTerm x y (i + 3)) := by
  have hs := ((summable_nat_add_iff 3).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))).mul_left
      ((49 / 40 : ℝ) * (x ^ 2 + y ^ 2) / gap (3 / 8) 3)
  apply Summable.of_nonneg_of_le
    (fun i => div_nonneg (sq_nonneg _) (by
      exact mul_nonneg (sq_nonneg _) (gap_pos (3 / 8) (by norm_num) (i + 3) (by omega)).le))
    _ hs
  intro i
  simpa only [fiveGramTerm, mul_one_div] using fiveGramTerm_le x y 3 (i + 3) le_rfl (by omega)

theorem five_complete_tail_le (x y : ℝ) :
    (∑' i : ℕ, fiveGramTerm x y (i + 37)) ≤ (1813 / 18540 : ℝ) * (x ^ 2 + y ^ 2) := by
  have hs := (summable_nat_add_iff 34).mpr (fiveGram_summable x y)
  simp only [Nat.add_assoc] at hs
  have hbase := (summable_nat_add_iff 37).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  have hg := gap_pos (3 / 8) (by norm_num) 37 (by norm_num)
  have hC : 0 ≤ (49 / 40 : ℝ) * (x ^ 2 + y ^ 2) / gap (3 / 8) 37 := by positivity
  calc
    _ ≤ ∑' i : ℕ, ((49 / 40 : ℝ) * (x ^ 2 + y ^ 2) / gap (3 / 8) 37) *
        (1 / ((i + 37 : ℕ) : ℝ) ^ 2) := by
      apply Summable.tsum_le_tsum _ hs (hbase.mul_left _)
      intro i
      simpa only [fiveGramTerm, mul_one_div] using fiveGramTerm_le x y 37 (i + 37) (by norm_num) (by omega)
    _ = _ * (∑' i : ℕ, 1 / ((i + 37 : ℕ) : ℝ) ^ 2) := by rw [tsum_mul_left]
    _ ≤ _ * (1 / 36) := mul_le_mul_of_nonneg_left inverseSquare_tail_le hC
    _ = _ := by norm_num [gap]; ring

theorem five_head_exact (x y : ℝ) :
    (∑ i : Fin 34, fiveGramTerm x y (i.val + 3)) =
      ((5 / 8 : ℝ) * finiteGram (3 / 8) weightOneFive weightOneFive) * x ^ 2 +
      2 * (Real.sqrt (5 / 8 : ℝ) * Real.sqrt (1 / 32 : ℝ) *
        finiteGram (3 / 8) weightOneFive weightTwoFive) * x * y +
      ((1 / 32 : ℝ) * finiteGram (3 / 8) weightTwoFive weightTwoFive) * y ^ 2 := by
  have hs1 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 8)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 32)
  have hterm (k : ℕ) : fiveGramTerm x y k =
      (5 / 8 : ℝ) * x ^ 2 * (weightOneFive k * weightOneFive k /
        ((k : ℝ) ^ 2 * gap (3 / 8) k)) +
      (2 * (Real.sqrt (5 / 8 : ℝ) * Real.sqrt (1 / 32 : ℝ)) * x * y) *
        (weightOneFive k * weightTwoFive k / ((k : ℝ) ^ 2 * gap (3 / 8) k)) +
      (1 / 32 : ℝ) * y ^ 2 * (weightTwoFive k * weightTwoFive k /
        ((k : ℝ) ^ 2 * gap (3 / 8) k)) := by
    unfold fiveGramTerm fiveCharge
    simp only [add_sq, mul_pow, hs1, hs2]
    ring
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold finiteGram
  ring

theorem five_complete_gram_le (x y : ℝ) :
    (∑' i : ℕ, fiveGramTerm x y (i + 3)) ≤ (3329 / 3708 : ℝ) * (x ^ 2 + y ^ 2) := by
  have hsplit := (fiveGram_summable x y).sum_add_tsum_nat_add 34
  rw [← Fin.sum_univ_eq_sum_range] at hsplit
  simp only [Nat.add_assoc] at hsplit
  rw [five_head_exact] at hsplit
  have hc : (Real.sqrt (5 / 8 : ℝ) * Real.sqrt (1 / 32 : ℝ) *
      finiteGram (3 / 8) weightOneFive weightTwoFive) ^ 2 ≤ 41 / 10000 := by
    simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 8),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 32)]
    nlinarith [normalized_head12_sq_le]
  have h := headTail_quadratic_le _ _ _ _ x y normalized_head11_le normalized_head22_le hc
    (five_complete_tail_le x y)
  linarith

end RiemannResearch.RH.ReciprocalConductorFiveCertificate
