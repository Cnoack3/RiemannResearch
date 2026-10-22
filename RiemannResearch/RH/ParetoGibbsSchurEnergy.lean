import RiemannResearch.RH.ParetoGibbsSchurGamma
import Mathlib.Algebra.BigOperators.Field

/-!
# Exact Schur square completion with all row tails

The positive Gamma weight has already been evaluated on the entire infinite
row. The identity below keeps every finite mixed term and the exact mass of
the omitted part of each row before deriving the uniform quadratic bound.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

private theorem schurWeight_ne (n : ℕ) : gibbsSchurWeight n ≠ 0 :=
  ne_of_gt (gibbsSchurWeight_pos n)

def gibbsSchurRow (n : ℕ) : ℝ :=
  ∑' m, gibbsComplementKernel n m * gibbsSchurWeight m

def gibbsSchurFiniteRow (s : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ m ∈ s, gibbsComplementKernel n m * gibbsSchurWeight m

private theorem schur_square_pair (n m : ℕ) (x y : ℝ) :
    gibbsComplementKernel n m * gibbsSchurWeight n * gibbsSchurWeight m *
      (x / gibbsSchurWeight n - y / gibbsSchurWeight m) ^ 2 =
    gibbsComplementKernel n m * (gibbsSchurWeight m / gibbsSchurWeight n) * x ^ 2 +
      gibbsComplementKernel n m * (gibbsSchurWeight n / gibbsSchurWeight m) * y ^ 2 -
      2 * (x * y * gibbsComplementKernel n m) := by
  field_simp [schurWeight_ne]
  <;> ring

theorem gibbsSchur_finite_square_completion (s : Finset ℕ) (v : ℕ → ℝ) (q : ℝ) :
    q * (∑ n ∈ s, v n ^ 2) -
        (∑ n ∈ s, ∑ m ∈ s, v n * v m * gibbsComplementKernel n m) =
      (∑ n ∈ s, (q - gibbsSchurFiniteRow s n / gibbsSchurWeight n) * v n ^ 2) +
      (1/2 : ℝ) * (∑ n ∈ s, ∑ m ∈ s,
        gibbsComplementKernel n m * gibbsSchurWeight n * gibbsSchurWeight m *
          (v n / gibbsSchurWeight n - v m / gibbsSchurWeight m) ^ 2) := by
  have hswap : (∑ n ∈ s, ∑ m ∈ s,
      gibbsComplementKernel n m * (gibbsSchurWeight n / gibbsSchurWeight m) * v m ^ 2) =
      ∑ n ∈ s, ∑ m ∈ s,
        gibbsComplementKernel n m * (gibbsSchurWeight m / gibbsSchurWeight n) * v n ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    rw [gibbsComplementKernel_symm]
  have hrow : (∑ n ∈ s, ∑ m ∈ s,
      gibbsComplementKernel n m * (gibbsSchurWeight m / gibbsSchurWeight n) * v n ^ 2) =
      ∑ n ∈ s, (gibbsSchurFiniteRow s n / gibbsSchurWeight n) * v n ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    unfold gibbsSchurFiniteRow
    simp_rw [Finset.sum_div, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have he : (∑ n ∈ s, ∑ m ∈ s,
      gibbsComplementKernel n m * gibbsSchurWeight n * gibbsSchurWeight m *
        (v n / gibbsSchurWeight n - v m / gibbsSchurWeight m) ^ 2) =
      2 * (∑ n ∈ s, (gibbsSchurFiniteRow s n / gibbsSchurWeight n) * v n ^ 2) -
      2 * (∑ n ∈ s, ∑ m ∈ s, v n * v m * gibbsComplementKernel n m) := by
    simp_rw [schur_square_pair, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rw [hswap, hrow]
    ring
  rw [he]
  simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Exact square completion, including the entire omitted mass of each row. -/
theorem gibbsSchur_full_row_square_completion (s : Finset ℕ) (v : ℕ → ℝ) (q : ℝ) :
    q * (∑ n ∈ s, v n ^ 2) -
        (∑ n ∈ s, ∑ m ∈ s, v n * v m * gibbsComplementKernel n m) =
      (∑ n ∈ s, (q - gibbsSchurRow n / gibbsSchurWeight n) * v n ^ 2) +
      (1/2 : ℝ) * (∑ n ∈ s, ∑ m ∈ s,
        gibbsComplementKernel n m * gibbsSchurWeight n * gibbsSchurWeight m *
          (v n / gibbsSchurWeight n - v m / gibbsSchurWeight m) ^ 2) +
      ∑ n ∈ s, ((gibbsSchurRow n - gibbsSchurFiniteRow s n) / gibbsSchurWeight n) * v n ^ 2 := by
  rw [gibbsSchur_finite_square_completion]
  have he (n : ℕ) : (q - gibbsSchurFiniteRow s n / gibbsSchurWeight n) * v n ^ 2 =
      (q - gibbsSchurRow n / gibbsSchurWeight n) * v n ^ 2 +
        ((gibbsSchurRow n - gibbsSchurFiniteRow s n) / gibbsSchurWeight n) * v n ^ 2 := by ring
  simp_rw [he, Finset.sum_add_distrib]
  ring

theorem gibbsSchurFiniteRow_le (s : Finset ℕ) (n : ℕ) :
    gibbsSchurFiniteRow s n ≤ gibbsSchurRow n := by
  exact (gibbsSchurGamma_row_hasSum n).summable.sum_le_tsum s
    (fun m hm => mul_nonneg (gibbsComplementKernel_pos n m).le (gibbsSchurWeight_pos m).le)

/-- The analytic pi/4 Schur bound, uniformly for every signed finite-support vector. -/
theorem gibbsComplementKernel_quadratic_le (s : Finset ℕ) (v : ℕ → ℝ) :
    (∑ n ∈ s, ∑ m ∈ s, v n * v m * gibbsComplementKernel n m) ≤
      (Real.pi / 4) * (∑ n ∈ s, v n ^ 2) := by
  apply sub_nonneg.mp
  rw [gibbsSchur_full_row_square_completion]
  apply add_nonneg
  · apply add_nonneg
    · apply Finset.sum_nonneg
      intro n hn
      apply mul_nonneg _ (sq_nonneg _)
      apply sub_nonneg.mpr
      apply (div_le_iff₀ (gibbsSchurWeight_pos n)).2
      exact gibbsSchurGamma_row_le n
    · apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro n hn
      apply Finset.sum_nonneg
      intro m hm
      exact mul_nonneg (mul_nonneg
        (mul_nonneg (gibbsComplementKernel_pos n m).le (gibbsSchurWeight_pos n).le)
        (gibbsSchurWeight_pos m).le) (sq_nonneg _)
  · apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (div_nonneg (sub_nonneg.mpr (gibbsSchurFiniteRow_le s n))
      (gibbsSchurWeight_pos n).le) (sq_nonneg _)

end
end RiemannResearch.RH.Pareto
