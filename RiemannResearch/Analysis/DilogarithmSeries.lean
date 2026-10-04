import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The real dilogarithm power series on the unit interval

Source: NIST DLMF 25.12.1, https://dlmf.nist.gov/25.12.E1.
This file uses the defining power series and proves its convergence and
geometric bounds, without introducing a branch outside [0,1).
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.DilogarithmSeries

def term (r : ℝ) (n : ℕ) : ℝ := r ^ (n+1) / ((n+1 : ℕ) : ℝ)^2
def value (r : ℝ) : ℝ := ∑' n : ℕ, term r n

theorem denominator_ge_one (n : ℕ) : 1 ≤ (((n+1 : ℕ) : ℝ)^2) := by
  have h : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  nlinarith

theorem term_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : 0 ≤ term r n :=
  div_nonneg (pow_nonneg hr _) (sq_nonneg _)

theorem term_le_pow {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    term r n ≤ r^(n+1) := by
  exact div_le_self (pow_nonneg hr _) (denominator_ge_one n)

theorem summable_term {r : ℝ} (hr : 0 ≤ r) (h1 : r < 1) :
    Summable (term r) := by
  have hs : Summable (fun n : ℕ => r^(n+1)) := by
    simpa [pow_succ, mul_comm] using
      (hasSum_geometric_of_lt_one hr h1).summable.mul_left r
  exact Summable.of_nonneg_of_le (term_nonneg hr) (term_le_pow hr) hs

theorem shifted_geometric {r : ℝ} (hr : 0 ≤ r) (h1 : r < 1) :
    (∑' n : ℕ, r^(n+1)) = r/(1-r) := by
  simpa [pow_succ, mul_comm, div_eq_mul_inv] using
    ((hasSum_geometric_of_lt_one hr h1).mul_left r).tsum_eq

theorem value_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ value r :=
  tsum_nonneg (term_nonneg hr)

theorem value_le_geometric {r : ℝ} (hr : 0 ≤ r) (h1 : r < 1) :
    value r ≤ r/(1-r) := by
  have hs : Summable (fun n : ℕ => r^(n+1)) := by
    simpa [pow_succ, mul_comm] using
      (hasSum_geometric_of_lt_one hr h1).summable.mul_left r
  rw [← shifted_geometric hr h1]
  exact (summable_term hr h1).tsum_le_tsum (term_le_pow hr) hs

end RiemannResearch.Analysis.DilogarithmSeries
