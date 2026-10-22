/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# An unconditional squarefree exact-head linear-energy benchmark

Source: Christian Noack's squarefree infinite CRT continuation,
16 October 2026, Section 9, for the prime-correction benchmark.
The existing canonical Mobius candidate, complete Pareto energy bound,
and actual Q/P norm transfer supply the proof strategy.

For every requested positive head H, choose H < p <= 2H and truncate
the canonical candidate at N = p - 1. Its correction conductor N+1 is
prime, so all nonzero conductors are squarefree. The candidate equals one
through N, hence through H. Every infinite physical tail is retained.

RH consumer: the resulting complete Q-error is O(H), unconditionally.
The existing QSquarefreeSublinearHeads module also gives asymptotic o(N)
energy. Here the explicit bound holds at every positive requested head.
The subpolynomial energy provider in QExactHeadSubpolynomial remains Open.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeLinearBenchmark
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer

/-- Transfer the established full Pareto energy bound, retaining the entire
physical sequence. No RH hypothesis is present. -/
theorem exactHead_norm_sq_lt_linear (N : ℕ) (hN : 0 < N) :
    ‖QMobiusExactHead.exactHead N‖ ^ 2 < 8 * (N : ℝ) / zetaTwo := by
  have ht := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq (QMobiusExactHead.exactHead N)
  rw [QSquarefreeSublinearHeads.toPareto_exactHead] at ht
  have hp := Pareto.canonicalMobiusHilbert_norm_sq_lt_four_mul N hN
  apply (lt_div_iff₀ zetaTwo_pos).mpr
  nlinarith

/-- Complete squared approximation error, not a finite-tail truncation. -/
theorem exactHead_error_sq_le_linear (N : ℕ) (hN : 0 < N) :
    ‖qOne - QMobiusExactHead.exactHead N‖ ^ 2 ≤ 2 + 16 * (N : ℝ) / zetaTwo := by
  have hn := norm_sub_le qOne (QMobiusExactHead.exactHead N)
  rw [qOne_norm] at hn
  have hs := mul_self_le_mul_self
    (norm_nonneg (qOne - QMobiusExactHead.exactHead N)) hn
  have he : ‖qOne - QMobiusExactHead.exactHead N‖ ^ 2 ≤
      2 + 2 * ‖QMobiusExactHead.exactHead N‖ ^ 2 := by
    nlinarith [sq_nonneg (1 - ‖QMobiusExactHead.exactHead N‖)]
  have hb := exactHead_norm_sq_lt_linear N hN
  calc
    _ ≤ 2 + 2 * ‖QMobiusExactHead.exactHead N‖ ^ 2 := he
    _ ≤ 2 + 2 * (8 * (N : ℝ) / zetaTwo) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hb.le (by norm_num))
    _ = _ := by ring

/-- Every positive requested head has a finite squarefree legal canonical
trial, using a cutoff below twice that head and a complete linear Q-error
bound. Neither uniform boundedness nor subpolynomial growth is asserted. -/
theorem exists_exactHead_linear_error (H : ℕ) (hH : 0 < H) :
    ∃ N : ℕ, H ≤ N ∧ N < 2 * H ∧ (N + 1).Prime ∧
      QMobiusExactHead.exactHead N ∈ qSquarefreeCRTSpan ∧
      (∀ n, 0 < n → n ≤ H → qSequence (QMobiusExactHead.exactHead N) n = 1) ∧
      ‖qOne - QMobiusExactHead.exactHead N‖ ^ 2 ≤
        2 + 32 * (H : ℝ) / zetaTwo := by
  obtain ⟨p, hp, hHp, hpH⟩ :=
    Nat.exists_prime_lt_and_le_two_mul H (ne_of_gt hH)
  let N := p - 1
  have hp2 := hp.two_le
  have hN : 0 < N := by dsimp [N]; omega
  have hNp : N + 1 = p := by dsimp [N]; omega
  have hHN : H ≤ N := by dsimp [N]; omega
  have hN2 : N < 2 * H := by dsimp [N]; omega
  have hprime : (N + 1).Prime := by simpa only [hNp] using hp
  refine ⟨N, hHN, hN2, hprime,
    QSquarefreeSublinearHeads.exactHead_mem_squarefreeSpan N hprime.squarefree, ?_, ?_⟩
  · intro n hn hnH
    exact QMobiusExactHead.exactHead_exact N n hn (hnH.trans hHN)
  · have hN2R : (N : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hN2.le
    have hnum : 16 * (N : ℝ) / zetaTwo ≤ 32 * (H : ℝ) / zetaTwo :=
      div_le_div_of_nonneg_right (by nlinarith) zetaTwo_pos.le
    exact (exactHead_error_sq_le_linear N hN).trans (add_le_add le_rfl hnum)

end RiemannResearch.RH.QSquarefreeLinearBenchmark
