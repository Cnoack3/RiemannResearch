/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.NearbyDilationGram
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete physical Q tails and bounded functions

Source: the user's residual-tail analysis, 25 October 2026.
These statements hold for every QHilbert vector; no squarefree orthogonality
or projection hypothesis is used. The exact series precedes the upper bound.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QAnnihilatorTailEscape
open ZetaTwoHilbert ZetaTwoProbability QFiniteSupportDualCriterion

/-- The tail is the complete weighted physical tail, with no truncation. -/
theorem tail_energy_physical (N : ℕ) (u : QHilbert) :
    ‖tail N u‖ ^ 2 = ∑' k : ℕ,
      positiveQWeight (k + N + 1) * qSequence u (k + N + 1) ^ 2 := by
  have happ (n : ℕ) : tail N u n = if N ≤ n then u n else 0 := by
    change u n - finiteHead N u n = _
    by_cases hn : N ≤ n
    · rw [finiteHead_apply_eq_zero N u n hn, if_pos hn, sub_zero]
    · rw [finiteHead_apply_of_lt N u n (by omega), if_neg hn, sub_self]
  have hs := (qCoordinate_square_summable (tail N u)).sum_add_tsum_nat_add N
  have hz : (∑ n ∈ Finset.range N, (tail N u n) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' := Finset.mem_range.mp hn
    rw [happ, if_neg (by omega)]
    norm_num
  rw [hz, zero_add] at hs
  calc
    ‖tail N u‖ ^ 2 = ∑' k : ℕ, (tail N u (k + N)) ^ 2 :=
      (qNorm_sq (tail N u)).trans hs.symm
    _ = _ := by
      apply tsum_congr
      intro k
      rw [happ, if_pos (by omega : N ≤ k + N)]
      exact (qSequence_weighted_square u (k + N)).symm

/-- A bounded physical function has a complete Q tail of order at most 1/N. -/
theorem zeta_mul_tail_energy_le_of_bounded (u : QHilbert) (N : ℕ)
    (C : ℝ) (_hC : 0 ≤ C) (hu : ∀ k : ℕ, |qSequence u k| ≤ C) :
    zetaTwo * ‖tail N u‖ ^ 2 ≤ 2 * C ^ 2 / ((N : ℝ) + 1) := by
  have hq : Summable (fun k : ℕ =>
      positiveQWeight (k + (N + 1)) * qSequence u (k + (N + 1)) ^ 2) :=
    (summable_nat_add_iff
      (f := fun k : ℕ => positiveQWeight k * qSequence u k ^ 2) (N + 1)).mpr
      (qSequence_square_summable u)
  have hp : Summable (fun k : ℕ => Pareto.positiveWeight (k + (N + 1))) :=
    (summable_nat_add_iff (f := Pareto.positiveWeight) (N + 1)).mpr
      Pareto.positiveWeight_summable
  have hb (k : ℕ) :
      zetaTwo * (positiveQWeight (k + (N + 1)) *
        qSequence u (k + (N + 1)) ^ 2) ≤
      Pareto.positiveWeight (k + (N + 1)) * (2 * C ^ 2) := by
    have hs : qSequence u (k + (N + 1)) ^ 2 ≤ C ^ 2 := by
      have ht := mul_self_le_mul_self (abs_nonneg (qSequence u (k + (N + 1))))
        (hu (k + (N + 1)))
      nlinarith [sq_abs (qSequence u (k + (N + 1)))]
    have hw := ZetaTwoParetoTransfer.zetaTwo_mul_QWeight_le_two_mul_paretoWeight
      (k + (N + 1))
    calc
      _ = (zetaTwo * positiveQWeight (k + (N + 1))) *
          qSequence u (k + (N + 1)) ^ 2 := by ring
      _ ≤ (2 * Pareto.positiveWeight (k + (N + 1))) *
          qSequence u (k + (N + 1)) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
      _ ≤ (2 * Pareto.positiveWeight (k + (N + 1))) * C ^ 2 :=
        mul_le_mul_of_nonneg_left hs
          (mul_nonneg (by norm_num) (Pareto.positiveWeight_nonneg _))
      _ = _ := by ring
  have h := (hq.mul_left zetaTwo).tsum_le_tsum hb (hp.mul_right (2 * C ^ 2))
  rw [tsum_mul_left, tsum_mul_right,
    Pareto.positiveWeight_tail_tsum (N + 1) (by omega)] at h
  rw [tail_energy_physical]
  simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, one_div,
    div_eq_mul_inv, mul_comm, one_mul] using h

theorem scaled_tail_energy_le_of_bounded (u : QHilbert) (N : ℕ)
    (C : ℝ) (hC : 0 ≤ C) (hu : ∀ k : ℕ, |qSequence u k| ≤ C) :
    (N : ℝ) * ‖tail N u‖ ^ 2 ≤ 2 * C ^ 2 / zetaTwo := by
  have h := zeta_mul_tail_energy_le_of_bounded u N C hC hu
  have hden : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hh := (le_div_iff₀ hden).mp h
  apply (le_div_iff₀ zetaTwo_pos).mpr
  have hnonneg : 0 ≤ zetaTwo * ‖tail N u‖ ^ 2 :=
    mul_nonneg zetaTwo_pos.le (sq_nonneg _)
  nlinarith


end RiemannResearch.RH.QAnnihilatorTailEscape
