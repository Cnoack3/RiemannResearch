import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite sums over positive multiples

Source: the existing finite reindexing proof in
`RH/ReciprocalChargeDilationArithmetic`. The unchanged statement and proof
are shared by reciprocal-charge applications and divisor convolutions.
-/

open scoped BigOperators

namespace RiemannResearch.NumberTheory

/-- Reindex an arbitrary finite sum over positive multiples. -/
theorem positive_dilation_sum (M h : ℕ) (hh : 0 < h) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 M, if h ∣ n then f (n / h) else 0) =
      ∑ d ∈ Finset.Icc 1 (M / h), f d := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun n _ => n / h) ?_ ?_ ?_ ?_
  · intro n hn
    have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hhn := (Finset.mem_filter.mp hn).2
    apply Finset.mem_Icc.mpr
    constructor
    · apply (Nat.le_div_iff_mul_le hh).mpr
      simpa using Nat.le_of_dvd (show 0 < n by omega) hhn
    · exact Nat.div_le_div_right hnI.2
  · intro n hn m hm he
    have hnq := Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
    have hmq := Nat.div_mul_cancel (Finset.mem_filter.mp hm).2
    calc
      n = (n / h) * h := hnq.symm
      _ = (m / h) * h := by rw [he]
      _ = m := hmq
  · intro d hd
    have hdI := Finset.mem_Icc.mp hd
    have hdM : d * h ≤ M := (Nat.le_div_iff_mul_le hh).mp hdI.2
    have hdvd : h ∣ d * h := ⟨d, by ring⟩
    have hq : (d * h) / h = d := by
      apply Nat.eq_of_mul_eq_mul_left hh
      simpa only [Nat.mul_comm] using Nat.div_mul_cancel hdvd
    refine ⟨d * h, Finset.mem_filter.mpr ⟨?_, hdvd⟩, hq⟩
    exact Finset.mem_Icc.mpr ⟨by nlinarith, hdM⟩
  · intro n hn
    rfl

end RiemannResearch.NumberTheory
