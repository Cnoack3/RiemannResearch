import RiemannResearch.RH.QResolventHarmonicPrefix

/-! # Harmonic sums on arbitrary finite sets and resolvent error at every depth

The finite-set bound applies to shells. The prefix comparison from
`QResolventHarmonicPrefix` gives a depth-dependent bound in terms of the
actual displacement norm, which may be bounded using any legal trial vector. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementResolvent

/-- Sum of absolute normalized physical coordinates on an arbitrary finite set. -/
theorem physicalHarmonic_finset_le (u : QHilbert) (s : Finset ℕ) :
    (∑ n ∈ s, |qSequence u n / (n : ℝ)|) ≤
      Real.sqrt (zetaTwo * (s.card : ℝ)) * ‖u‖ := by
  have hfin := sq_sum_le_card_mul_sum_sq (s := s)
    (f := fun n : ℕ => |qSequence u n / (n : ℝ)|)
  simp only [sq_abs] at hfin
  have hnorm : (∑ n ∈ s, (qSequence u n / (n : ℝ)) ^ 2) ≤ zetaTwo * ‖u‖ ^ 2 := by
    rw [qNorm_weighted_sq]
    calc
      _ = ∑ n ∈ s, zetaTwo * (positiveQWeight n * (qSequence u n)^2) := by
        apply Finset.sum_congr rfl
        intro n _
        by_cases hn : n = 0
        · simp [hn]
        · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
          unfold positiveQWeight
          field_simp [hn', zetaTwo_pos.ne']
      _ = zetaTwo * (∑ n ∈ s, positiveQWeight n * (qSequence u n)^2) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((qSequence_square_summable u).sum_le_tsum s
          (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))) zetaTwo_pos.le
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  rw [mul_pow, Real.sq_sqrt (mul_nonneg zetaTwo_pos.le (Nat.cast_nonneg _))]
  calc
    _ ≤ _ := hfin
    _ ≤ (s.card : ℝ) * (zetaTwo * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Uniform difference of the actual and approximating smaller sign masses. -/
theorem harmonic_resolvent_error_le (X j : ℕ) :
    |minimumHarmonicPrefix X - minimumHarmonicPrefixOf (resolventApprox j) X| ≤
      Real.sqrt (zetaTwo * (X : ℝ)) * ((1/3 : ℝ)^j * ‖displacement‖) := by
  rw [Real.sqrt_mul zetaTwo_pos.le, mul_comm (Real.sqrt zetaTwo) (Real.sqrt (X : ℝ))]
  exact (minimumHarmonicPrefixOf_error displacement (resolventApprox j) X).trans
    (mul_le_mul_of_nonneg_left (resolvent_error_norm_le j)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

/-- Adaptive-depth comparison without growth in the cutoff. -/
theorem harmonic_resolvent_adaptive_error (X j : ℕ) (hX : X ≤ 9^j) :
    |minimumHarmonicPrefix X - minimumHarmonicPrefixOf (resolventApprox j) X| ≤
      Real.sqrt zetaTwo * ‖displacement‖ := by
  apply (harmonic_resolvent_error_le X j).trans
  have h9 : (X : ℝ) ≤ (9 : ℝ)^j := by exact_mod_cast hX
  have heq : (9 : ℝ)^j = ((3 : ℝ)^j)^2 := by
    rw [show (9 : ℝ) = 3^2 by norm_num, ← pow_mul, Nat.mul_comm, pow_mul]
  have hroot := Real.sqrt_le_sqrt (h9.trans_eq heq)
  rw [Real.sqrt_sq (by positivity)] at hroot
  have hprod : Real.sqrt (X : ℝ) * (1/3 : ℝ)^j ≤ 1 := by
    rw [one_div, inv_pow, ← div_eq_mul_inv]
    exact (div_le_one (by positivity)).mpr hroot
  rw [Real.sqrt_mul zetaTwo_pos.le]
  calc
    _ = Real.sqrt zetaTwo * ((Real.sqrt (X : ℝ) * (1/3 : ℝ)^j) * ‖displacement‖) := by ring
    _ ≤ Real.sqrt zetaTwo * (1 * ‖displacement‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod (norm_nonneg _))
        (Real.sqrt_nonneg _)
    _ = _ := by ring

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
