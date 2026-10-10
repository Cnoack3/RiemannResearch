import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The actual twin-prime Euler product

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

The Euler factors are indexed by every natural number; nonprimes and two
have factor one. Convergence and strict positivity are unconditional and
do not imply any assertion about actual prime-pair correlations.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RiemannResearch.NumberTheory.PrimePairEulerProduct

def primePairEulerFactor (p : ℕ) : ℝ :=
  if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

def twinPrimeConstant : ℝ := ∏' p : ℕ, primePairEulerFactor p

private theorem one_add_factor_sub_one (p : ℕ) :
    1 + (primePairEulerFactor p - 1) = primePairEulerFactor p := by ring

theorem primePairEulerFactor_pos (p : ℕ) : 0 < primePairEulerFactor p := by
  by_cases hp : Nat.Prime p ∧ 2 < p
  · have hpR : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2
    have hd : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos (by linarith)
    have hd1 : 1 < ((p : ℝ) - 1) ^ 2 := by
      nlinarith [sq_nonneg ((p : ℝ) - 2)]
    have hi : 1 / ((p : ℝ) - 1) ^ 2 < (1 : ℝ) :=
      (div_lt_one hd).2 hd1
    simp only [primePairEulerFactor, if_pos hp]
    linarith
  · simp [primePairEulerFactor, hp]

theorem primePairEulerFactor_le_one (p : ℕ) : primePairEulerFactor p ≤ 1 := by
  by_cases hp : Nat.Prime p ∧ 2 < p
  · simp only [primePairEulerFactor, if_pos hp]
    have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith
  · simp [primePairEulerFactor, hp]

/-- A bound by the ordinary square-reciprocal series avoids requiring any
estimate for the distribution of primes. The value at zero is harmless. -/
theorem norm_primePairEulerFactor_sub_one_le (p : ℕ) :
    ‖primePairEulerFactor p - 1‖ ≤ 4 / (p : ℝ) ^ 2 := by
  by_cases hp : Nat.Prime p ∧ 2 < p
  · have hpR : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2
    have hd : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos (by linarith)
    have hp2 : 0 < (p : ℝ) ^ 2 := sq_pos_of_pos (by linarith)
    have hs : (p : ℝ) ^ 2 ≤ 4 * ((p : ℝ) - 1) ^ 2 := by
      nlinarith [sq_nonneg ((p : ℝ) - 2)]
    have hdiff : primePairEulerFactor p - 1 = -(1 / ((p : ℝ) - 1) ^ 2) := by
      simp only [primePairEulerFactor, if_pos hp]
      ring
    rw [hdiff, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_le_div_iff₀ hd hp2).2 (by simpa using hs)
  · simp only [primePairEulerFactor, if_neg hp, sub_self, norm_zero]
    positivity

theorem summable_norm_primePairEulerFactor_sub_one :
    Summable (fun p : ℕ => ‖primePairEulerFactor p - 1‖) := by
  have hbase : Summable (fun p : ℕ => 1 / (p : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hbound : Summable (fun p : ℕ => 4 / (p : ℝ) ^ 2) := by
    simpa only [mul_one_div] using hbase.mul_left (4 : ℝ)
  exact hbound.of_nonneg_of_le (fun _ => norm_nonneg _)
    norm_primePairEulerFactor_sub_one_le

theorem primePairEulerFactor_multipliable : Multipliable primePairEulerFactor := by
  simpa only [one_add_factor_sub_one] using
    multipliable_one_add_of_summable summable_norm_primePairEulerFactor_sub_one

theorem twinPrimeConstant_ne_zero : twinPrimeConstant ≠ 0 := by
  unfold twinPrimeConstant
  simpa only [one_add_factor_sub_one] using
    tprod_one_add_ne_zero_of_summable
      (f := fun p : ℕ => primePairEulerFactor p - 1)
      (fun p => by simpa only [one_add_factor_sub_one] using
        (ne_of_gt (primePairEulerFactor_pos p)))
      summable_norm_primePairEulerFactor_sub_one

theorem twinPrimeConstant_pos : 0 < twinPrimeConstant := by
  have hn : 0 ≤ twinPrimeConstant :=
    ge_of_tendsto' primePairEulerFactor_multipliable.hasProd.tendsto_prod_nat
      (fun N => Finset.prod_nonneg (fun p _ => (primePairEulerFactor_pos p).le))
  exact lt_of_le_of_ne hn (Ne.symm twinPrimeConstant_ne_zero)

theorem summable_log_primePairEulerFactor :
    Summable (fun p : ℕ => Real.log (primePairEulerFactor p)) := by
  have h := Real.summable_log_one_add_of_summable
    summable_norm_primePairEulerFactor_sub_one.of_norm
  simpa only [one_add_factor_sub_one] using h

theorem twinPrimeConstant_eq_exp_tsum_log :
    twinPrimeConstant = Real.exp (∑' p : ℕ, Real.log (primePairEulerFactor p)) := by
  exact (Real.rexp_tsum_eq_tprod primePairEulerFactor_pos
    summable_log_primePairEulerFactor).symm

theorem twinPrimeConstant_le_finite_product (s : Finset ℕ) :
    twinPrimeConstant ≤ ∏ p ∈ s, primePairEulerFactor p := by
  have hnonpos (p : ℕ) : Real.log (primePairEulerFactor p) ≤ 0 :=
    Real.log_nonpos (primePairEulerFactor_pos p).le (primePairEulerFactor_le_one p)
  have hneg := summable_log_primePairEulerFactor.neg.sum_le_tsum s
    (fun p _ => neg_nonneg.mpr (hnonpos p))
  rw [Finset.sum_neg_distrib, tsum_neg] at hneg
  have hsum : (∑' p : ℕ, Real.log (primePairEulerFactor p)) ≤
      ∑ p ∈ s, Real.log (primePairEulerFactor p) := by linarith
  rw [twinPrimeConstant_eq_exp_tsum_log]
  calc
    Real.exp (∑' p : ℕ, Real.log (primePairEulerFactor p)) ≤
        Real.exp (∑ p ∈ s, Real.log (primePairEulerFactor p)) :=
      Real.exp_le_exp.mpr hsum
    _ = ∏ p ∈ s, primePairEulerFactor p := by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro p _
      exact Real.exp_log (primePairEulerFactor_pos p)

theorem primePairEulerFactor_three : primePairEulerFactor 3 = (3 / 4 : ℝ) := by
  norm_num [primePairEulerFactor]

theorem twinPrimeConstant_le_three_quarters : twinPrimeConstant ≤ (3 / 4 : ℝ) := by
  simpa only [Finset.prod_singleton, primePairEulerFactor_three] using
    twinPrimeConstant_le_finite_product {3}

theorem twinPrimeConstant_le_five_prime_product :
    twinPrimeConstant ≤ (11011 / 16384 : ℝ) := by
  have hfinite :
      (∏ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), primePairEulerFactor p) =
        (11011 / 16384 : ℝ) := by
    norm_num [primePairEulerFactor]
  simpa only [hfinite] using
    twinPrimeConstant_le_finite_product {3, 5, 7, 11, 13}

/-- The product over all integers starting with three is a telescoping
minorant. Omitting composite factors can only increase the actual product. -/
private theorem integer_product_formula (N : ℕ) :
    (∏ n ∈ Finset.range N, (1 - 1 / ((n : ℝ) + 2) ^ 2)) =
      ((N : ℝ) + 2) / (2 * ((N : ℝ) + 1)) := by
  induction N with
  | zero => norm_num
  | succ N hN =>
      rw [Finset.prod_range_succ, hN]
      simp only [Nat.cast_succ]
      rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
      have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
      have hn2 : (N : ℝ) + 2 ≠ 0 := by positivity
      field_simp [hn1, hn2]
      ring

private theorem integer_factor_nonneg (n : ℕ) :
    0 ≤ (1 - 1 / ((n : ℝ) + 2) ^ 2) := by
  have hd : 0 < ((n : ℝ) + 2) ^ 2 := by positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd1 : 1 ≤ ((n : ℝ) + 2) ^ 2 := by
    nlinarith
  exact sub_nonneg.mpr ((div_le_one hd).2 hd1)

private theorem integer_factor_le_prime_factor (n : ℕ) :
    (1 - 1 / ((n : ℝ) + 2) ^ 2) ≤ primePairEulerFactor (n + 3) := by
  by_cases hp : Nat.Prime (n + 3) ∧ 2 < n + 3
  · have he : ((n + 3 : ℕ) : ℝ) - 1 = (n : ℝ) + 2 := by
      push_cast
      ring
    simp only [primePairEulerFactor, if_pos hp, he, le_refl]
  · simp only [primePairEulerFactor, if_neg hp]
    have : 0 ≤ 1 / ((n : ℝ) + 2) ^ 2 := by positivity
    linarith

private theorem prime_product_prefix (N : ℕ) :
    (∏ p ∈ Finset.range (N + 3), primePairEulerFactor p) =
      ∏ n ∈ Finset.range N, primePairEulerFactor (n + 3) := by
  induction N with
  | zero => norm_num [Finset.prod_range_succ, primePairEulerFactor]
  | succ N hN =>
      calc
        (∏ p ∈ Finset.range (N + 1 + 3), primePairEulerFactor p) =
            (∏ p ∈ Finset.range (N + 3), primePairEulerFactor p) *
              primePairEulerFactor (N + 3) := by
          rw [show N + 1 + 3 = (N + 3) + 1 by omega, Finset.prod_range_succ]
        _ = (∏ n ∈ Finset.range N, primePairEulerFactor (n + 3)) *
              primePairEulerFactor (N + 3) := by rw [hN]
        _ = ∏ n ∈ Finset.range (N + 1), primePairEulerFactor (n + 3) := by
          symm
          rw [Finset.prod_range_succ]

theorem one_half_le_primePairFiniteProduct (N : ℕ) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ Finset.range N, primePairEulerFactor p := by
  by_cases hN : 3 ≤ N
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [Nat.add_comm 3 M, prime_product_prefix]
    calc
      (1 / 2 : ℝ) ≤ ((M : ℝ) + 2) / (2 * ((M : ℝ) + 1)) := by
        apply (le_div_iff₀ (by positivity)).2
        nlinarith
      _ = ∏ n ∈ Finset.range M, (1 - 1 / ((n : ℝ) + 2) ^ 2) :=
        (integer_product_formula M).symm
      _ ≤ ∏ n ∈ Finset.range M, primePairEulerFactor (n + 3) :=
        Finset.prod_le_prod (fun n _ => integer_factor_nonneg n)
          (fun n _ => integer_factor_le_prime_factor n)
  · have hsmall : N = 0 ∨ N = 1 ∨ N = 2 := by omega
    rcases hsmall with rfl | rfl | rfl <;>
      norm_num [Finset.prod_range_succ, primePairEulerFactor]

theorem one_half_le_twinPrimeConstant : (1 / 2 : ℝ) ≤ twinPrimeConstant := by
  exact ge_of_tendsto' primePairEulerFactor_multipliable.hasProd.tendsto_prod_nat
    one_half_le_primePairFiniteProduct

end RiemannResearch.NumberTheory.PrimePairEulerProduct
