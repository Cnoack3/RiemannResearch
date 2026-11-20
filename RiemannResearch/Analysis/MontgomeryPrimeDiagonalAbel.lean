/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalTransition
import RiemannResearch.Analysis.MontgomeryPrimeCrossIntegral
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Abel summation for the Montgomery prime diagonal

These identities isolate the summatory function needed for the diagonal estimate.
The corresponding weighted prime-power decomposition appears in Garunkštis and
Paliulionytė, pp. 215–217, https://hrcak.srce.hr/en/file/495424 . -/

open MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction
noncomputable section
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel

/-- Excess of the `Λ(n) log n` prefix over its squared von Mangoldt prefix. -/
def mangoldtSquareCorrection (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n)

/-- The correction comes entirely from higher prime powers. -/
theorem mangoldtSquareCorrection_bound {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ mangoldtSquareCorrection x ∧
    mangoldtSquareCorrection x ≤ (Chebyshev.psi x - Chebyshev.theta x) * Real.log x := by
  constructor
  · exact Finset.sum_nonneg fun n _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (sub_nonneg.mpr ArithmeticFunction.vonMangoldt_le_log)
  · rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter,
      ← Finset.sum_sub_distrib, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n hn
    by_cases hp : n.Prime
    · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp only [hp, if_false, sub_zero]
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      have hnx : (n : ℝ) ≤ x := (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans
        (Nat.floor_le (by linarith : 0 ≤ x))
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      exact mul_le_mul_of_nonneg_left
        ((sub_le_self _ ArithmeticFunction.vonMangoldt_nonneg).trans (Real.log_le_log hnpos hnx))
        ArithmeticFunction.vonMangoldt_nonneg

/-- Chebyshev's estimate for `ψ - θ` bounds the higher-prime-power contribution. -/
theorem mangoldtSquareCorrection_le_sqrt_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
    mangoldtSquareCorrection x ≤ C * Real.sqrt x * Real.log x := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  exact ⟨C, by simpa using hC 1, fun x hx => (mangoldtSquareCorrection_bound hx).2.trans
    (mul_le_mul_of_nonneg_right (hC x) (Real.log_nonneg hx))⟩

/-- Abel summation for the squared prefix, retaining the exact prime-power correction. -/
theorem mangoldtSquarePrefix_abel {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n ^ 2 =
      Real.log x * Chebyshev.psi x -
      (∫ t in Ioc 1 x, (Chebyshev.psi t)/t) - mangoldtSquareCorrection x := by
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) : DifferentiableAt ℝ Real.log t :=
    (Real.hasDerivAt_log (by linarith [ht.1])).differentiableAt
  have hc : ContinuousOn (deriv Real.log) (Icc 1 x) := by
    rw [Real.deriv_log']
    exact continuousOn_id.inv₀ fun t ht => by change t ≠ 0; linarith [ht.1]
  have ha := sum_mul_eq_sub_integral_mul₀ (fun n : ℕ => Λ n)
    (by simp) x hd hc.integrableOn_Icc
  have hi :
      (∫ t in Ioc 1 x, deriv Real.log t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, Λ n) =
      ∫ t in Ioc 1 x, (Chebyshev.psi t) / t := by
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.deriv_log, ← Chebyshev.psi_eq_sum_Icc]
    ring
  rw [hi, ← Chebyshev.psi_eq_sum_Icc] at ha
  rw [← ha, mangoldtSquareCorrection, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Square of the prime weight on either side of its matching frequency. -/
theorem primeWeight_sq_edge_kernel {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (MontgomeryPrimeCrossIntegral.primeWeight x n)^2 =
      if (n : ℝ) ≤ x then (Λ n)^2 * n / x^2 else (Λ n)^2 * x^2 / (n : ℝ)^3 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [MontgomeryPrimeCrossIntegral.primeWeight]
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  rw [MontgomeryPrimeCrossIntegral.primeWeight]
  by_cases h : (n : ℝ) ≤ x
  · rw [if_pos h, min_eq_left ((div_le_div_iff₀ hx hn).mpr (mul_self_le_mul_self hn.le h)),
      mul_pow, div_pow, div_pow, Real.sq_sqrt hn.le]
    field_simp [hx.ne', hn.ne'] <;> ring
  · rw [if_neg h, min_eq_right ((div_le_div_iff₀ hn hx).mpr
      (mul_self_le_mul_self hx.le (le_of_lt (lt_of_not_ge h)))),
      mul_pow, div_pow, div_pow, Real.sq_sqrt hn.le]
    field_simp [hx.ne', hn.ne'] <;> ring

/-- The diagonal as a sum of the two branches of its exact weight. -/
theorem primeDiagonal_eq_edge_kernel {x : ℝ} (hx : 0 < x) :
    primeDiagonal x = ∑' n : ℕ,
      if (n : ℝ) ≤ x then (Λ n)^2 * n / x^2 else (Λ n)^2 * x^2 / (n : ℝ)^3 :=
  tsum_congr fun n => primeWeight_sq_edge_kernel hx n

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
