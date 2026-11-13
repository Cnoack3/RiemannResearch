import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# An elementary finite Euler-product tail bound

Source: the Pareto Dirichlet-exponential argument.  We dominate each tail
factor by an exponential and telescope reciprocal differences.  The bound
is deliberately uniform in the finite endpoint.
-/

namespace RiemannResearch.NumberTheory.DirichletExponential

open scoped BigOperators

private theorem reciprocal_square_le_difference {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  have heq : 1 / (x * (x + 1)) = 1 / x - 1 / (x + 1) := by
    field_simp
    ring
  rw [← heq]
  exact one_div_le_one_div_of_le (mul_pos hx hx1) (by nlinarith)

/-- The reciprocal-square tail bound follows from a finite telescoping sum. -/
theorem sum_reciprocal_square_tail_le (r m : ℕ) (hr : 0 < r) :
    (∑ k ∈ Finset.range m, 1 / (2 * (r : ℝ) + k + 1) ^ 2) ≤
      1 / (2 * (r : ℝ)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hs (m : ℕ) :
      (∑ k ∈ Finset.range m, 1 / (2 * (r : ℝ) + k + 1) ^ 2) ≤
        1 / (2 * (r : ℝ)) - 1 / (2 * (r : ℝ) + m) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have ht := reciprocal_square_le_difference
        (show 0 < 2 * (r : ℝ) + m by positivity)
      simp only [Nat.cast_add, Nat.cast_one, ← add_assoc] at *
      linarith
  exact (hs m).trans (sub_le_self _ (by positivity))

private theorem reciprocal_one_sub_le_exp {x : ℝ}
    (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    1 / (1 - x) ≤ Real.exp (2 * x) := by
  have hd : 0 < 1 - x := by linarith
  calc
    1 / (1 - x) ≤ 1 + 2 * x := by
      apply (div_le_iff₀ hd).2
      have hp := mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)
      nlinarith
    _ ≤ Real.exp (2 * x) := by
      simpa only [add_comm] using Real.add_one_le_exp (2 * x)

/-- Each sufficiently late local factor is dominated by an exponential. -/
theorem euler_tail_factor_le_exp (r k : ℕ) (hr : 0 < r) :
    (2 * (r : ℝ) + k + 1) ^ 2 /
        ((2 * (r : ℝ) + k + 1) ^ 2 - (r : ℝ) ^ 2) ≤
      Real.exp (2 * (r : ℝ) ^ 2 / (2 * (r : ℝ) + k + 1) ^ 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  let n : ℝ := 2 * r + k + 1
  have hn : 0 < n := by dsimp [n]; positivity
  have hn2 : 0 < n ^ 2 := sq_pos_of_pos hn
  have hhalf : (r : ℝ) ^ 2 / n ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ hn2).2
    dsimp [n]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [sq_nonneg ((k : ℝ) + 1)]
  have hid : n ^ 2 / (n ^ 2 - (r : ℝ) ^ 2) =
      1 / (1 - (r : ℝ) ^ 2 / n ^ 2) := by
    field_simp
  have h := reciprocal_one_sub_le_exp
    (div_nonneg (sq_nonneg (r : ℝ)) hn2.le) hhalf
  rw [← hid] at h
  simpa only [n, mul_div_assoc] using h

/-- A finite product of the large-prime majorants is bounded uniformly by
`exp r`.  Primes can subsequently be enlarged to this whole integer interval. -/
theorem euler_tail_range_product_le (r m : ℕ) (hr : 0 < r) :
    (∏ k ∈ Finset.range m,
      (2 * (r : ℝ) + k + 1) ^ 2 /
        ((2 * (r : ℝ) + k + 1) ^ 2 - (r : ℝ) ^ 2)) ≤ Real.exp r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  calc
    _ ≤ ∏ k ∈ Finset.range m,
        Real.exp (2 * (r : ℝ) ^ 2 / (2 * (r : ℝ) + k + 1) ^ 2) := by
      apply Finset.prod_le_prod
      · intro k hk
        apply div_nonneg (sq_nonneg _)
        have hkn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith [sq_nonneg ((k : ℝ) + 1)]
      · intro k hk
        exact euler_tail_factor_le_exp r k hr
    _ = Real.exp (∑ k ∈ Finset.range m,
        2 * (r : ℝ) ^ 2 / (2 * (r : ℝ) + k + 1) ^ 2) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp r := by
      apply Real.exp_le_exp.mpr
      have hs := mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail_le r m hr)
        (show 0 ≤ 2 * (r : ℝ) ^ 2 by positivity)
      have heq : 2 * (r : ℝ) ^ 2 * (1 / (2 * (r : ℝ))) = r := by
        field_simp <;> ring
      rw [heq] at hs
      simpa only [Finset.mul_sum, mul_one_div] using hs

/-- Interval form of the finite Euler-product tail estimate. -/
theorem euler_tail_product_le (r N : ℕ) (hr : 0 < r) :
    (∏ n ∈ Finset.Icc (2 * r + 1) N,
      (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - (r : ℝ) ^ 2)) ≤ Real.exp r := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  have h := euler_tail_range_product_le r ((N + 1) - (2 * r + 1)) hr
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    add_assoc, add_left_comm, add_comm] using h

end RiemannResearch.NumberTheory.DirichletExponential
