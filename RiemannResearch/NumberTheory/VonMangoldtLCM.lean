import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact von Mangoldt arithmetic for the running LCM

Mathlib already supplies the prime-valuation theorem
`Nat.factorization_lcmUpto` and the classical logarithmic identity
`Chebyshev.psi_eq_log_lcmUpto`. We reuse them rather than duplicate them.

This module supplies their exact prime-power increments and the signed
Möbius floor formula. The concrete RH consumer is the finite arithmetic
step in the damping variation described in research agenda target 2 of
`Q_Squarefree_RH_VonMangoldt_LCM_Research_Agenda_2026-10-16.md`.

Sources: the user's research agenda (16 October 2026) for the application;
Mathlib's `NumberTheory/Chebyshev.lean` for the valuation/log-LCM statements
and `ArithmeticFunction.sum_moebius_mul_log_eq` for Möbius inversion.
The classical log-LCM identity is also recorded in the introduction of
Hong, Qian, and Tan, *The least common multiple of a sequence of products
of linear polynomials*, https://arxiv.org/abs/1108.0162v2.
These references support the statements and proof strategy, not a novelty claim.

All results are unconditional finite arithmetic identities. No Hilbert
differentiability, uniform remainder estimate, or RH theorem is asserted.
-/

noncomputable section

open scoped BigOperators

namespace Nat

/-- The p-adic exponent of the running LCM counts the positive powers of p
that have appeared by the cutoff. -/
theorem factorization_lcmUpto_eq_card_prime_powers (N : ℕ) {p : ℕ}
    (hp : p.Prime) :
    (lcmUpto N).factorization p =
      ((Finset.Icc 1 N).filter (fun k => p ^ k ≤ N)).card := by
  rw [factorization_lcmUpto N hp]
  by_cases hN : N = 0
  · subst N
    simp
  have hfilter :
      (Finset.Icc 1 N).filter (fun k => p ^ k ≤ N) =
        Finset.Icc 1 (p.log N) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk, _⟩, hpow⟩
      exact ⟨hk, (Nat.le_log_iff_pow_le hp.one_lt hN).mpr hpow⟩
    · rintro ⟨hk, hlog⟩
      exact ⟨⟨hk, hlog.trans (Nat.log_le_self p N)⟩,
        Nat.pow_le_of_le_log hN hlog⟩
  rw [hfilter]
  simp

/-- The exact log-LCM increment, including every prime-power jump. -/
theorem log_lcmUpto_succ_sub (n : ℕ) :
    Real.log (lcmUpto (n + 1) : ℝ) - Real.log (lcmUpto n : ℝ) =
      ArithmeticFunction.vonMangoldt (n + 1) := by
  rw [← Chebyshev.psi_eq_log_lcmUpto, ← Chebyshev.psi_eq_log_lcmUpto]
  have hi : Finset.Ioc 0 (n + 1) =
      insert (n + 1) (Finset.Ioc 0 n) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  simp only [Chebyshev.psi, Nat.floor_natCast, hi]
  rw [Finset.sum_insert (by simp)]
  linarith

/-- Positive-index version of the log-LCM increment. -/
theorem log_lcmUpto_sub_pred {n : ℕ} (hn : 0 < n) :
    Real.log (lcmUpto n : ℝ) - Real.log (lcmUpto (n - 1) : ℝ) =
      ArithmeticFunction.vonMangoldt n := by
  have hs : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simpa only [hs] using log_lcmUpto_succ_sub (n - 1)

/-- At p^k the running LCM is multiplied by exactly p. -/
theorem lcmUpto_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    lcmUpto (p ^ k) = p * lcmUpto (p ^ k - 1) := by
  have h := log_lcmUpto_sub_pred (pow_pos hp.pos k)
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp] at h
  have he :
      Real.log (lcmUpto (p ^ k) : ℝ) =
        Real.log (p : ℝ) + Real.log (lcmUpto (p ^ k - 1) : ℝ) := by
    linarith
  have hC : (0 : ℝ) < lcmUpto (p ^ k) := by
    exact_mod_cast lcmUpto_pos (p ^ k)
  have hD : (0 : ℝ) < lcmUpto (p ^ k - 1) := by
    exact_mod_cast lcmUpto_pos (p ^ k - 1)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hexp := congrArg Real.exp he
  rw [Real.exp_log hC, Real.exp_add, Real.exp_log hpR,
    Real.exp_log hD] at hexp
  exact_mod_cast hexp

/-- The running LCM stays unchanged exactly at non-prime-powers. -/
theorem lcmUpto_eq_pred_iff_not_isPrimePow {n : ℕ} (hn : 0 < n) :
    lcmUpto n = lcmUpto (n - 1) ↔ ¬ IsPrimePow n := by
  have heq :
      lcmUpto n = lcmUpto (n - 1) ↔
        Real.log (lcmUpto n : ℝ) -
          Real.log (lcmUpto (n - 1) : ℝ) = 0 := by
    constructor
    · intro h
      rw [h, sub_self]
    · intro h
      have hlog :
          Real.log (lcmUpto n : ℝ) =
            Real.log (lcmUpto (n - 1) : ℝ) := by linarith
      have hC : (0 : ℝ) < lcmUpto n := by
        exact_mod_cast lcmUpto_pos n
      have hD : (0 : ℝ) < lcmUpto (n - 1) := by
        exact_mod_cast lcmUpto_pos (n - 1)
      have hexp := congrArg Real.exp hlog
      rw [Real.exp_log hC, Real.exp_log hD] at hexp
      exact_mod_cast hexp
  rw [heq, log_lcmUpto_sub_pred hn]
  exact ArithmeticFunction.vonMangoldt_eq_zero_iff

/-- Equivalently, the running LCM changes precisely at prime powers. -/
theorem lcmUpto_ne_pred_iff_isPrimePow {n : ℕ} (hn : 0 < n) :
    lcmUpto n ≠ lcmUpto (n - 1) ↔ IsPrimePow n := by
  simp only [ne_eq, lcmUpto_eq_pred_iff_not_isPrimePow hn, not_not]

end Nat

namespace Chebyshev

/-- The summatory von Mangoldt function as the complete signed Möbius floor
sum. The quotient is natural-number division before casting to the reals. -/
theorem psi_nat_eq_neg_sum_moebius_log_mul_div (N : ℕ) :
    psi (N : ℝ) =
      -(∑ d ∈ Finset.Ioc 0 N,
        (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
          ((N / d : ℕ) : ℝ)) := by
  let f : ArithmeticFunction ℝ :=
    ⟨fun d => (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ), by simp⟩
  have hf (n : ℕ) :
      (f * ArithmeticFunction.zeta) n =
        -ArithmeticFunction.vonMangoldt n := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    change (∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) =
        -ArithmeticFunction.vonMangoldt n
    simpa only [ArithmeticFunction.log_apply] using
      (ArithmeticFunction.sum_moebius_mul_log_eq (n := n))
  have hs := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum f N
  simp only [hf, Finset.sum_neg_distrib] at hs
  change -(∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n) =
    ∑ d ∈ Finset.Ioc 0 N,
      (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
        ((N / d : ℕ) : ℝ) at hs
  simp only [psi, Nat.floor_natCast]
  linarith

end Chebyshev

namespace Nat

/-- Exact finite arithmetic bridge from the running LCM to squarefree-supported
Möbius coefficients. No absolute values or discarded boundary terms occur. -/
theorem log_lcmUpto_eq_neg_sum_moebius_log_mul_div (N : ℕ) :
    Real.log (lcmUpto N : ℝ) =
      -(∑ d ∈ Finset.Ioc 0 N,
        (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
          ((N / d : ℕ) : ℝ)) := by
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  exact Chebyshev.psi_nat_eq_neg_sum_moebius_log_mul_div N

/-- Exponentiating the full signed floor identity recovers the integer LCM. -/
theorem cast_lcmUpto_eq_exp_neg_sum_moebius_log_mul_div (N : ℕ) :
    (lcmUpto N : ℝ) =
      Real.exp (-(∑ d ∈ Finset.Ioc 0 N,
        (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
          ((N / d : ℕ) : ℝ))) := by
  rw [← log_lcmUpto_eq_neg_sum_moebius_log_mul_div]
  exact (Real.exp_log (by exact_mod_cast lcmUpto_pos N)).symm

/-- The exact signed Möbius product for the running LCM. Integer negative
exponents are retained; the product is evaluated in the positive reals. -/
theorem cast_lcmUpto_eq_prod_moebius_zpow (N : ℕ) :
    (lcmUpto N : ℝ) =
      ∏ d ∈ Finset.Ioc 0 N,
        (d : ℝ) ^ (-(ArithmeticFunction.moebius d) * ((N / d : ℕ) : ℤ)) := by
  have hdpos (d : ℕ) (hd : d ∈ Finset.Ioc 0 N) : (0 : ℝ) < d := by
    exact_mod_cast (Finset.mem_Ioc.mp hd).1
  have hprod : (0 : ℝ) <
      ∏ d ∈ Finset.Ioc 0 N,
        (d : ℝ) ^ (-(ArithmeticFunction.moebius d) * ((N / d : ℕ) : ℤ)) := by
    exact Finset.prod_pos (fun d hd => zpow_pos (hdpos d hd) _)
  have hLCM : (0 : ℝ) < lcmUpto N := by
    exact_mod_cast lcmUpto_pos N
  apply Real.log_injOn_pos hLCM hprod
  rw [log_lcmUpto_eq_neg_sum_moebius_log_mul_div,
    Real.log_prod (fun d hd => zpow_ne_zero _ (hdpos d hd).ne'),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Real.log_zpow]
  simp only [Int.cast_mul, Int.cast_neg, Int.cast_natCast]
  ring

end Nat
