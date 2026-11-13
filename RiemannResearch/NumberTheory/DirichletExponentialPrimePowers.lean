import RiemannResearch.NumberTheory.DirichletExponential
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Prime-power coefficients of convolution powers of the constant atom

Source: the user-provided Pareto exponential argument. This file identifies
the universal arithmetic majorant with Mathlib's `ζ` and proves the exact
prime-power coefficients and their geometric bound.
-/

noncomputable section

namespace RiemannResearch.NumberTheory.DirichletExponential

open scoped BigOperators

/-- The constant-one function on the positive integers, with the required
arithmetic-function value zero at zero. This is distinct from `δ₁`. -/
abbrev zetaReal : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

@[simp] theorem zetaReal_apply (n : ℕ) :
    zetaReal n = if n = 0 then 0 else 1 := by
  by_cases hn : n = 0 <;> simp [zetaReal, ArithmeticFunction.zeta_apply, hn]

theorem zetaReal_nonneg (n : ℕ) : 0 ≤ zetaReal n := by
  rw [zetaReal_apply]
  split_ifs <;> norm_num

theorem zetaReal_abs_le_one (n : ℕ) : |zetaReal n| ≤ 1 := by
  rw [zetaReal_apply]
  split_ifs <;> norm_num

/-- Convolution powers of the universal majorant are multiplicative. -/
theorem zetaReal_pow_isMultiplicative (r : ℕ) :
    ArithmeticFunction.IsMultiplicative (zetaReal ^ r) :=
  (ArithmeticFunction.isMultiplicative_zeta.natCast).pow

/-- The number of multisets of cardinality `a` from an alphabet of size `r`
is at most the number of ordered words of length `a`. -/
theorem multichoose_le_pow (r a : ℕ) : r.multichoose a ≤ r ^ a := by
  cases r with
  | zero => cases a <;> simp
  | succ r =>
      simpa only [Nat.multichoose_eq, Nat.succ_add_sub_one] using
        Nat.choose_add_le_add_one_pow r a

/-- The exact generalized-divisor coefficient on a prime power. -/
theorem zetaReal_pow_prime_pow {p : ℕ} (hp : p.Prime) (r a : ℕ) :
    (zetaReal ^ r) (p ^ a) = (r.multichoose a : ℝ) := by
  induction r generalizing a with
  | zero =>
      cases a with
      | zero => simp
      | succ a =>
          simp [ArithmeticFunction.one_apply, hp.ne_one]
  | succ r ih =>
      calc
        (zetaReal ^ (r + 1)) (p ^ a)
            = ∑ j ∈ Finset.range (a + 1), (zetaReal ^ r) (p ^ j) := by
          rw [pow_succ, ArithmeticFunction.coe_mul_zeta_apply,
            Nat.sum_divisors_prime_pow hp]
        _ = ∑ j ∈ Finset.range (a + 1), (r.multichoose j : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact ih j
        _ = ((a + r).choose r : ℝ) := by
          exact_mod_cast Nat.sum_range_multichoose a r
        _ = ((r + 1).multichoose a : ℝ) := by
          congr 1
          rw [Nat.multichoose_eq]
          have hi : r + 1 + a - 1 = a + r := by omega
          rw [hi]
          exact (Nat.choose_symm_add (a := a) (b := r)).symm

/-- A binomial form adapted to the negative-binomial generating series. -/
theorem zetaReal_pow_succ_prime_pow {p : ℕ} (hp : p.Prime) (r a : ℕ) :
    (zetaReal ^ (r + 1)) (p ^ a) = ((a + r).choose r : ℝ) := by
  rw [zetaReal_pow_prime_pow hp, Nat.multichoose_eq]
  have hi : r + 1 + a - 1 = a + r := by omega
  rw [hi]
  congr 1
  exact Nat.choose_symm_add

/-- A geometric bound for each prime-power coefficient, used for the
large-prime Euler factors. -/
theorem zetaReal_pow_prime_pow_le {p : ℕ} (hp : p.Prime) (r a : ℕ) :
    (zetaReal ^ r) (p ^ a) ≤ (r : ℝ) ^ a := by
  rw [zetaReal_pow_prime_pow hp]
  exact_mod_cast multichoose_le_pow r a

end RiemannResearch.NumberTheory.DirichletExponential
