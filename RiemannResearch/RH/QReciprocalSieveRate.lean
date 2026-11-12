import RiemannResearch.RH.QReciprocalFullDensity
import RiemannResearch.RH.QReciprocalSieveNorm
import RiemannResearch.RH.QPrimeSieve
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Quantitative full-norm convergence of the factorial Mobius sieve
Source: D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf, Proposition 4.2.
The exact signed coprime-count identity is reused before estimating the tail.
The exact head n < m(N + 1) yields error squared at most 1 / (m ^ 3(N + 1)) in P.
This controls smoothed sieve vectors, not unsmoothed legal preimages.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QReciprocalSieveRate
open ZetaTwoHilbert ZetaTwoParetoTransfer QReciprocalFullDensity QReciprocalSieveNorm QPrimeSieve

theorem factorialSieve_exact_head (N m n : ℕ) (hm : 0 < m)
    (hn : n < m * (N + 1)) :
    qSequence (factorialSieve N m) n = qSequence (tailVector m) n := by
  rw [factorialSieve_sequence N m hm n, tailVector_sequence]
  by_cases hmn : m ≤ n
  · have hr : 0 < n / m := Nat.div_pos hmn hm
    have hdiv : n / m ≤ N := by
      have := (Nat.div_lt_iff_lt_mul hm).mpr (by simpa [Nat.mul_comm] using hn)
      omega
    rw [coprimeCount_head N.factorial N (n / m) hr hdiv (factorial_covers_head N)]
    simp [tailSequence, hmn]
  · have hr : n / m = 0 := Nat.div_eq_of_lt (by omega)
    simp [hr, coprimeCount, ArithmeticCumulative.cumulative, tailSequence, hmn]

theorem tailSequence_le_inv (m n : ℕ) (hm : 0 < m) :
    tailSequence m n ≤ 1 / (m : ℝ) := by
  unfold tailSequence
  split_ifs with hmn
  · exact div_le_div_of_nonneg_left zero_le_one (by exact_mod_cast hm)
      (by exact_mod_cast hmn)
  · positivity

theorem factorialSieve_pareto_error_sq_le (N m : ℕ) (hm : 0 < m) :
    ‖toPareto (factorialSieve N m - tailVector m)‖ ^ 2 ≤
      1 / ((m : ℝ) ^ 3 * ((N : ℝ)+1)) := by
  have he (n : ℕ) : qSequence (factorialSieve N m - tailVector m) n =
      qSequence (factorialSieve N m) n - qSequence (tailVector m) n := by
    change qSequenceLinear (_-_) n = _
    rw [map_sub]
    rfl
  calc
    _ ≤ (1 / (m : ℝ)) ^ 2 / ((m * (N + 1) : ℕ) : ℝ) := by
      apply pareto_norm_sq_le_of_tail_bound _ (m * (N + 1)) (by positivity) _ (by positivity)
      · intro n hn
        rw [he, factorialSieve_exact_head N m n hm hn, sub_self]
      · intro n hn
        rw [he]
        have hs := factorialSieve_bounds N m hm n
        have ht := tailSequence_bounds m n
        have hb := tailSequence_le_inv m n hm
        rw [tailVector_sequence]
        exact abs_le.mpr ⟨by linarith [hs.1, hb], by linarith [hs.2, ht.1]⟩
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Transfer of the certified complete sieve error to Q. -/
theorem factorialSieve_q_error_sq_le (N m : ℕ) (hm : 0 < m) :
    ‖factorialSieve N m - tailVector m‖ ^ 2 ≤
      (2 / ZetaTwoProbability.zetaTwo) / ((m : ℝ) ^ 3 * ((N : ℝ) + 1)) := by
  have h := QParetoEquivalence.toQ_norm_sq_le
    (toPareto (factorialSieve N m - tailVector m))
  rw [QParetoEquivalence.toQ_toPareto] at h
  calc
    _ ≤ (2 / ZetaTwoProbability.zetaTwo) *
        ‖toPareto (factorialSieve N m - tailVector m)‖ ^ 2 := h
    _ ≤ (2 / ZetaTwoProbability.zetaTwo) *
        (1 / ((m : ℝ) ^ 3 * ((N : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (factorialSieve_pareto_error_sq_le N m hm)
        (by positivity [ZetaTwoProbability.zetaTwo_pos])
    _ = _ := by ring

end RiemannResearch.RH.QReciprocalSieveRate
