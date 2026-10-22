import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.Mertens
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Linarith

/-!
# An unconditional explicit prime-power covariance row budget

Source: the weighted-Schur proof in the user manuscript
`Prime_Phases_Agenda_Proof_Attempts.tex`, Theorem `growing-phase-gram`.
The Mertens provider is already proved in the project's port of Goldmakher's
elementary proof; no PNT or zero-distribution hypothesis is introduced here.

The row budget keeps every positive integer frequency, including composite
frequencies. Identifying this expression with the weighted absolute row of
the original square-root covariance matrix is a separate algebraic identity.
-/

open scoped BigOperators ArithmeticFunction

namespace RiemannResearch.Fourier

/-- The full directed row after conjugation by n^{-1/2}; diagonal contributions
    vanish because Lambda(1)=0. Both multiples and divisors are retained. -/
noncomputable def primePowerCovarianceDirectedEntry (n m : ℕ) : ℝ :=
  (if n ∣ m then ArithmeticFunction.vonMangoldt (m / n) / (m / n : ℕ) else 0) +
    (if m ∣ n then ArithmeticFunction.vonMangoldt (n / m) else 0)

/-- The upward-multiple and downward-divisor components of the full row. -/
noncomputable def primePowerCovarianceRowBudget (N n : ℕ) : ℝ :=
  (∑ q ∈ Finset.Ioc 0 (N / n), ArithmeticFunction.vonMangoldt q / (q : ℝ)) +
    ∑ q ∈ n.divisors, ArithmeticFunction.vonMangoldt q

/-- Every divisor contribution is retained exactly, and sums to log n. -/
theorem primePowerCovarianceRowBudget_eq (N n : ℕ) :
    primePowerCovarianceRowBudget N n =
      (∑ q ∈ Finset.Ioc 0 (N / n), ArithmeticFunction.vonMangoldt q / (q : ℝ)) +
        Real.log n := by
  rw [primePowerCovarianceRowBudget, ArithmeticFunction.vonMangoldt_sum]

private theorem sum_multiples_reindex (N n : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.Ioc 0 N,
      if n ∣ m then ArithmeticFunction.vonMangoldt (m / n) / (m / n : ℕ) else 0) =
      ∑ q ∈ Finset.Ioc 0 (N / n), ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun m _ => m / n)
  · intro m hm
    obtain ⟨hmI, hdvd⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmpos, hmN⟩ := Finset.mem_Ioc.mp hmI
    exact Finset.mem_Ioc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hmpos hdvd) hn, Nat.div_le_div_right hmN⟩
  · intro a ha b hb hab
    have hda := (Finset.mem_filter.mp ha).2
    have hdb := (Finset.mem_filter.mp hb).2
    have hmul := congrArg (fun q : ℕ => q * n) hab
    simpa only [Nat.div_mul_cancel hda, Nat.div_mul_cancel hdb] using hmul
  · intro q hq
    obtain ⟨hqpos, hqN⟩ := Finset.mem_Ioc.mp hq
    have hmul : n * q ≤ N := by
      have h := (Nat.le_div_iff_mul_le hn).mp hqN
      simpa only [mul_comm] using h
    refine ⟨n * q, Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨mul_pos hn hqpos, hmul⟩, dvd_mul_right n q⟩, ?_⟩
    exact Nat.mul_div_cancel_left q hn
  · intro m hm
    rfl

private theorem sum_divisors_complement (n : ℕ) :
    (∑ q ∈ n.divisors, ArithmeticFunction.vonMangoldt (n / q)) =
      ∑ q ∈ n.divisors, ArithmeticFunction.vonMangoldt q := by
  have hleft := Nat.sum_divisorsAntidiagonal
    (fun (_ : ℕ) (q : ℕ) => ArithmeticFunction.vonMangoldt q) (n := n)
  have hright := Nat.sum_divisorsAntidiagonal'
    (fun (_ : ℕ) (q : ℕ) => ArithmeticFunction.vonMangoldt q) (n := n)
  exact hleft.symm.trans hright

/-- Exact reindexing of the full integer-frequency row into its arithmetic
    budget. Composite integer frequencies are never discarded. -/
theorem sum_primePowerCovarianceDirectedEntry_eq (N n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    (∑ m ∈ Finset.Ioc 0 N, primePowerCovarianceDirectedEntry n m) =
      primePowerCovarianceRowBudget N n := by
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn0 : n ≠ 0 := hnpos.ne'
  have hfilter : (Finset.Ioc 0 N).filter (fun m => m ∣ n) = n.divisors := by
    ext m
    constructor
    · intro hm
      exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hm).2, hn0⟩
    · intro hm
      have hmn := Nat.dvd_of_mem_divisors hm
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
        ⟨Nat.pos_of_mem_divisors hm, le_trans (Nat.divisor_le hm) hnN⟩, hmn⟩
  unfold primePowerCovarianceDirectedEntry primePowerCovarianceRowBudget
  rw [Finset.sum_add_distrib, sum_multiples_reindex N n hnpos]
  congr 1
  rw [← Finset.sum_filter, hfilter, sum_divisors_complement]

theorem primePowerCovarianceDirectedEntry_nonneg (n m : ℕ) :
    0 ≤ primePowerCovarianceDirectedEntry n m := by
  unfold primePowerCovarianceDirectedEntry
  positivity

/-- The manuscript's O(1) in the covariance Schur budget can be replaced by
    the explicit unconditional constant log 4 + 4. -/
theorem primePowerCovarianceRowBudget_le (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    primePowerCovarianceRowBudget N n ≤ Real.log N + Real.log 4 + 4 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hnpos (by exact_mod_cast hnN)
  have hratio : (1 : ℝ) ≤ (N : ℝ) / (n : ℝ) :=
    (one_le_div hnpos).mpr (by exact_mod_cast hnN)
  have hm := Mertens.E₁Λ.le hratio
  change (∑ q ∈ Finset.Ioc 0 ⌊(N : ℝ) / n⌋₊,
    ArithmeticFunction.vonMangoldt q / (q : ℝ)) - Real.log ((N : ℝ) / n) ≤
      Real.log 4 + 4 at hm
  rw [Nat.floor_div_natCast, Nat.floor_natCast] at hm
  rw [Real.log_div hNpos.ne' hnpos.ne'] at hm
  rw [primePowerCovarianceRowBudget_eq]
  linarith

end RiemannResearch.Fourier
