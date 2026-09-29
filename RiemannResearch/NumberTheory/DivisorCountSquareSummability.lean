import RiemannResearch.NumberTheory.DivisorCountSummability
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# Summability of squared divisor counts

Pairing each divisor above sqrt(n) with its complementary divisor proves
tau(n) <= 2 sqrt(n). The existing divisor-count Dirichlet series at exponent
3/2 then supplies square summability with denominator n^2.

Concrete RH consumer: dominated convergence of the complete natural-cutoff
Mobius derivative residual in the Pareto Hilbert norm.
Source: the user-directed vanishing attempt; elementary divisor pairing and
the repository's Dirichlet-convolution summability provider.
-/

namespace RiemannResearch.NumberTheory

theorem divisor_count_le_two_mul_nat_sqrt (n : ℕ) :
    n.divisors.card ≤ 2 * n.sqrt := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  have hs : n.divisors ⊆ Finset.Icc 1 n.sqrt ∪
      (Finset.Icc 1 n.sqrt).image (fun d => n / d) := by
    intro d hd
    have hdp : 0 < d := Nat.pos_of_mem_divisors hd
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
    by_cases hdsmall : d ≤ n.sqrt
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hdp, hdsmall⟩)
    · have he : n / d * d = n := Nat.div_mul_cancel hdn
      have hqp : 0 < n / d := by
        apply Nat.pos_of_ne_zero
        intro hz
        rw [hz, zero_mul] at he
        exact hn he.symm
      have hqsmall : n / d ≤ n.sqrt := by
        by_contra hq
        have hdlarge : n.sqrt + 1 ≤ d := by omega
        have hqlarge : n.sqrt + 1 ≤ n / d := by omega
        have hp := Nat.mul_le_mul hqlarge hdlarge
        have hlt := Nat.lt_succ_sqrt n
        rw [he] at hp
        exact (not_lt_of_ge hp) (by simpa only [Nat.succ_eq_add_one] using hlt)
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨n / d, Finset.mem_Icc.mpr ⟨hqp, hqsmall⟩, ?_⟩
      calc
        n / (n / d) = (n / d * d) / (n / d) := by rw [he]
        _ = d := by rw [Nat.mul_comm]; exact Nat.mul_div_cancel d hqp
  calc
    n.divisors.card ≤ (Finset.Icc 1 n.sqrt ∪
        (Finset.Icc 1 n.sqrt).image (fun d => n / d)).card := Finset.card_le_card hs
    _ ≤ (Finset.Icc 1 n.sqrt).card +
        ((Finset.Icc 1 n.sqrt).image (fun d => n / d)).card := Finset.card_union_le _ _
    _ ≤ (Finset.Icc 1 n.sqrt).card + (Finset.Icc 1 n.sqrt).card :=
      Nat.add_le_add_left (Finset.card_image_le) _
    _ = 2 * n.sqrt := by simp; omega

theorem divisor_count_le_two_mul_sqrt (n : ℕ) :
    (n.divisors.card : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  have hn : (n.divisors.card : ℝ) ≤ 2 * (n.sqrt : ℝ) := by
    exact_mod_cast divisor_count_le_two_mul_nat_sqrt n
  exact hn.trans (mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by norm_num))

/-- Squared divisor counts are Pareto summable by one ordinary convolution
at exponent 3/2 and the elementary divisor-pairing bound. -/
theorem summable_divisor_count_sq_div_sq :
    Summable (fun n : ℕ => (n.divisors.card : ℝ)^2 / (n : ℝ)^2) := by
  have hs := (summable_divisor_count_div_rpow (3 / 2) (by norm_num)).mul_left 2
  apply hs.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    by_cases hn : n = 0
    · simp [hn]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hns : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnR)
    have hb := mul_le_mul_of_nonneg_right (divisor_count_le_two_mul_sqrt n)
      (Nat.cast_nonneg n.divisors.card : (0 : ℝ) ≤ n.divisors.card)
    calc
      (n.divisors.card : ℝ)^2 / (n : ℝ)^2 ≤
          (2 * Real.sqrt (n : ℝ) * (n.divisors.card : ℝ)) / (n : ℝ)^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        nlinarith
      _ = 2 * ((n.divisors.card : ℝ) / (n : ℝ)^(3 / 2 : ℝ)) := by
        rw [show (3 / 2 : ℝ) = 2 - 1 / 2 by norm_num,
          Real.rpow_sub hnR, Real.rpow_two, ← Real.sqrt_eq_rpow]
        field_simp [ne_of_gt hnR, hns]

/-- A majorant that includes the reciprocal-source term as well as every
truncated signed divisor term in the raw Möbius difference. -/
theorem summable_one_add_divisor_count_sq_div_sq :
    Summable (fun n : ℕ => (1 + (n.divisors.card : ℝ))^2 / (n : ℝ)^2) := by
  have hp : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)^2) := by
    simpa only [Real.rpow_two] using
      (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 2))
  apply ((hp.add summable_divisor_count_sq_div_sq).mul_left 2).of_nonneg_of_le
  · intro n
    positivity
  · intro n
    calc
      (1 + (n.divisors.card : ℝ))^2 / (n : ℝ)^2 ≤
          (2 * (1 + (n.divisors.card : ℝ)^2)) / (n : ℝ)^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        nlinarith [sq_nonneg ((n.divisors.card : ℝ) - 1)]
      _ = 2 * (1 / (n : ℝ)^2 + (n.divisors.card : ℝ)^2 / (n : ℝ)^2) := by ring

end RiemannResearch.NumberTheory
