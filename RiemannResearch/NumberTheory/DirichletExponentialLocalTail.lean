import RiemannResearch.NumberTheory.DirichletExponentialPrimePowers
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Large-prime Euler factors for generalized divisor moments

Source: the user-provided Pareto exponential argument. The geometric bound on
prime-power coefficients gives a summable local second-moment factor whenever
the prime exceeds the convolution-power index.
-/

noncomputable section

namespace RiemannResearch.NumberTheory.DirichletExponential

open scoped BigOperators

/-- Each squared prime-power term is bounded by a geometric term. -/
theorem zetaReal_pow_prime_pow_sq_term_le {p : ℕ} (hp : p.Prime) (r a : ℕ) :
    ((zetaReal ^ r) (p ^ a)) ^ 2 / ((p ^ a : ℕ) : ℝ) ^ 2
      ≤ ((r : ℝ) ^ 2 / (p : ℝ) ^ 2) ^ a := by
  have h0 : 0 ≤ (zetaReal ^ r) (p ^ a) := by
    rw [zetaReal_pow_prime_pow hp]
    positivity
  have hsq : ((zetaReal ^ r) (p ^ a)) ^ 2 ≤ ((r : ℝ) ^ a) ^ 2 :=
    (sq_le_sq₀ h0 (by positivity)).2 (zetaReal_pow_prime_pow_le hp r a)
  calc
    ((zetaReal ^ r) (p ^ a)) ^ 2 / ((p ^ a : ℕ) : ℝ) ^ 2
        ≤ ((r : ℝ) ^ a) ^ 2 / ((p ^ a : ℕ) : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hsq (by positivity)
    _ = ((r : ℝ) ^ 2 / (p : ℝ) ^ 2) ^ a := by
      simp only [Nat.cast_pow, div_pow, ← pow_mul, Nat.mul_comm a 2]

private theorem large_prime_ratio_abs_lt_one {p r : ℕ} (hp : p.Prime)
    (hrp : r < p) : |(r : ℝ) ^ 2 / (p : ℝ) ^ 2| < 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hrpR : (r : ℝ) < p := by exact_mod_cast hrp
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  apply (div_lt_one₀ (sq_pos_of_pos hpR)).2
  nlinarith

/-- A large-prime local second-moment series is absolutely summable. -/
theorem zetaReal_pow_prime_pow_sq_summable {p r : ℕ} (hp : p.Prime)
    (hrp : r < p) :
    Summable (fun a : ℕ =>
      ((zetaReal ^ r) (p ^ a)) ^ 2 / ((p ^ a : ℕ) : ℝ) ^ 2) := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_abs_lt_one (large_prime_ratio_abs_lt_one hp hrp))
  intro a
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact zetaReal_pow_prime_pow_sq_term_le hp r a

/-- The large-prime local Euler factor is at most the corresponding geometric
factor `1 / (1 - r²/p²)`. -/
theorem zetaReal_pow_prime_pow_sq_tsum_le {p r : ℕ} (hp : p.Prime)
    (hrp : r < p) :
    (∑' a : ℕ, ((zetaReal ^ r) (p ^ a)) ^ 2 / ((p ^ a : ℕ) : ℝ) ^ 2)
      ≤ 1 / (1 - (r : ℝ) ^ 2 / (p : ℝ) ^ 2) := by
  have hratio := large_prime_ratio_abs_lt_one hp hrp
  calc
    (∑' a : ℕ, ((zetaReal ^ r) (p ^ a)) ^ 2 / ((p ^ a : ℕ) : ℝ) ^ 2)
        ≤ ∑' a : ℕ, ((r : ℝ) ^ 2 / (p : ℝ) ^ 2) ^ a :=
      Summable.tsum_le_tsum (zetaReal_pow_prime_pow_sq_term_le hp r)
        (zetaReal_pow_prime_pow_sq_summable hp hrp)
        (summable_geometric_of_abs_lt_one hratio)
    _ = 1 / (1 - (r : ℝ) ^ 2 / (p : ℝ) ^ 2) := by
      rw [tsum_geometric_of_abs_lt_one hratio, one_div]

end RiemannResearch.NumberTheory.DirichletExponential
