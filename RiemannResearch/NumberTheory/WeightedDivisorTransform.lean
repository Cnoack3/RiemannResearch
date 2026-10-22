import RiemannResearch.RH.ArithmeticReturnConvolution

/-!
# Finite weighted divisor transforms

Source: the user-requested exact signed correction program. The finite
Dirichlet-convolution reindexing retains the product cutoff before the
nonnegative majorization. The RH consumer is WeightedDivisorCorrection.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.WeightedDivisorTransform

def divisorTransform (a x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.divisorsAntidiagonal, a p.2 * x p.1

/-- A finite Dirichlet-convolution inequality; the product cutoff is retained
until the final nonnegative majorization. -/
theorem finite_weighted_divisor_bound (a x w : ℕ → ℝ) (N : ℕ)
    (ha : ∀ k, |a k| ≤ 1) (hw : ∀ k, 0 ≤ w k)
    (hw0 : w 0 = 0) (hmul : ∀ k l, w (k * l) = w k * w l) :
    (∑ n ∈ Finset.range (N + 1), w n * |divisorTransform a x n|) ≤
      (∑ k ∈ Finset.range (N + 1), w k * |x k|) *
        ∑ l ∈ Finset.range (N + 1), w l := by
  let F : ℕ → ℕ → ℝ := fun k l => w k * |x k| * w l
  have hF0 : ∀ k, F 0 k = 0 := by intro k; simp [F, hw0]
  have hF1 : ∀ k, F k 0 = 0 := by intro k; simp [F, hw0]
  have hFn : ∀ k l, 0 ≤ F k l := by
    intro k l
    exact mul_nonneg (mul_nonneg (hw k) (abs_nonneg _)) (hw l)
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1),
        ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2 := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        w n * |divisorTransform a x n| ≤
            w n * ∑ p ∈ n.divisorsAntidiagonal, |a p.2 * x p.1| := by
          exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (hw n)
        _ ≤ w n * ∑ p ∈ n.divisorsAntidiagonal, |x p.1| := by
          apply mul_le_mul_of_nonneg_left _ (hw n)
          apply Finset.sum_le_sum
          intro p hp
          rw [abs_mul]
          simpa using mul_le_mul_of_nonneg_right (ha p.2) (abs_nonneg (x p.1))
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
          rw [← hp', hmul]
          dsimp [F]
          ring
    _ = ∑ k ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1),
        if k * l ≤ N then F k l else 0 :=
      Nat.sum_divisorsAntidiagonal_range N F hF0 hF1
    _ ≤ ∑ k ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1),
        F k l := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      split_ifs
      · exact le_rfl
      · exact hFn k l
    _ = _ := by
      simp only [F, Finset.sum_mul_sum]

def squareWeight (n : ℕ) : ℝ := 1 / (n : ℝ) ^ 2

theorem finite_mobius_squareWeight_bound (x : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), squareWeight n *
      |divisorTransform (fun k => (ArithmeticFunction.moebius k : ℝ)) x n|) ≤
      (∑ k ∈ Finset.range (N + 1), squareWeight k * |x k|) *
        ∑ l ∈ Finset.range (N + 1), squareWeight l := by
  apply finite_weighted_divisor_bound
  · intro k
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
  · intro k
    exact one_div_nonneg.mpr (sq_nonneg _)
  · norm_num [squareWeight]
  · intro k l
    simp only [squareWeight, Nat.cast_mul, mul_pow, one_div, mul_inv_rev]
    ring

end RiemannResearch.NumberTheory.WeightedDivisorTransform
