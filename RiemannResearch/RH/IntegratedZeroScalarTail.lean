import RiemannResearch.RH.WeilExplicitFormula.Tail.Count
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A telescoping logarithmic reciprocal-square tail

This is the missing scalar rate in the actual-zero unit-window argument.
The local zeta zero count is already proved in
`Zeta23.RvM.zetaZeroConfig_local_count`; no external Landau, Tsang, or RH
hypothesis is needed for the zero-series truncation bound.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.IntegratedZeroScalarTail

private theorem two_le_log_add_three {t : ℝ} (ht : 5 ≤ t) :
    2 ≤ Real.log (t + 3) := by
  have hexp : Real.exp 2 < 8 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have h1 := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    nlinarith
  apply (Real.le_log_iff_exp_le (by linarith : 0 < t + 3)).mpr
  linarith

/-- A logarithmic reciprocal square is bounded by a telescoping difference. -/
theorem scalar_step {t : ℝ} (ht : 5 ≤ t) :
    Real.log (t + 3) / t ^ 2 ≤
      4 * (Real.log (t + 3) / t - Real.log (t + 4) / (t + 1)) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t + 1 := by linarith
  have ht3 : 0 < t + 3 := by linarith
  have hL := two_le_log_add_three ht
  have hinc : Real.log (t + 4) ≤ Real.log (t + 3) + 1 / (t + 3) := by
    simpa only [add_assoc, show (3 : ℝ) + 1 = 4 by norm_num] using
      (Zeta23.Tail.log_add_le_log_add_div (B := t + 3) (j := 1) ht3
        (by norm_num))
  have hsmall : 1 / (t + 3) ≤ Real.log (t + 3) / (2 * t) := by
    rw [div_le_div_iff₀ ht3 (by positivity : 0 < 2 * t)]
    nlinarith
  have hdiff : Real.log (t + 3) / (2 * t * (t + 1)) ≤
      Real.log (t + 3) / t - Real.log (t + 4) / (t + 1) := by
    calc
      _ = Real.log (t + 3) / (t * (t + 1)) -
          (Real.log (t + 3) / (2 * t)) / (t + 1) := by
            field_simp
            ring
      _ ≤ Real.log (t + 3) / (t * (t + 1)) -
          (1 / (t + 3)) / (t + 1) := by
            gcongr
      _ = Real.log (t + 3) / t -
          (Real.log (t + 3) + 1 / (t + 3)) / (t + 1) := by
            field_simp
            ring
      _ ≤ Real.log (t + 3) / t - Real.log (t + 4) / (t + 1) := by
            gcongr
  have hden : Real.log (t + 3) / (4 * t ^ 2) ≤
      Real.log (t + 3) / (2 * t * (t + 1)) := by
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have h := hden.trans hdiff
  have heq : Real.log (t + 3) / t ^ 2 =
      4 * (Real.log (t + 3) / (4 * t ^ 2)) := by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- Finite tails telescope, including the terminal term. -/
theorem finite_tail_le_telescope (K n : ℕ) (hK : 5 ≤ K) :
    (∑ j ∈ Finset.range n,
      Real.log ((K + j : ℕ) + 3) / ((K + j : ℕ) : ℝ) ^ 2) ≤
    4 * (Real.log ((K : ℝ) + 3) / K -
      Real.log ((K + n : ℕ) + 3) / (K + n : ℕ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hstep := scalar_step (t := ((K + n : ℕ) : ℝ))
      (by exact_mod_cast (show 5 ≤ K + n by omega))
    have hn : ((K + (n + 1) : ℕ) : ℝ) = (K + n : ℕ) + 1 := by
      push_cast
      ring
    rw [hn]
    calc
      _ ≤ 4 * (Real.log ((K : ℝ) + 3) / K -
          Real.log ((K + n : ℕ) + 3) / (K + n : ℕ)) +
          4 * (Real.log ((K + n : ℕ) + 3) / (K + n : ℕ) -
            Real.log (((K + n : ℕ) : ℝ) + 4) / (((K + n : ℕ) : ℝ) + 1)) :=
        add_le_add ih hstep
      _ = _ := by ring

/-- Explicit scalar tail rate, uniform in the terminal cutoff. -/
theorem finite_tail_le (K n : ℕ) (hK : 5 ≤ K) :
    (∑ j ∈ Finset.range n,
      Real.log ((K + j : ℕ) + 3) / ((K + j : ℕ) : ℝ) ^ 2) ≤
      4 * Real.log ((K : ℝ) + 3) / K := by
  have hlog : 0 ≤ Real.log (((K + n : ℕ) : ℝ) + 3) :=
    Real.log_nonneg (by
      have hnn : (0 : ℝ) ≤ (K + n : ℕ) := Nat.cast_nonneg _
      linarith)
  have htail : 0 ≤ Real.log (((K + n : ℕ) : ℝ) + 3) / (K + n : ℕ) := by
    positivity
  have h := finite_tail_le_telescope K n hK
  rw [mul_div_assoc]
  nlinarith

end RiemannResearch.RH.IntegratedZeroScalarTail
