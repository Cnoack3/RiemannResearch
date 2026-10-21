/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerTransformRigidity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Prime valuations are outside the enlarged squarefree closure

Source: the user-provided floor-logarithm/valuation comparison, 21 October
2026, combined with this project's checked squarefree jump constraint.

The counting target F_p(n) = Nat.log p n and the valuation v_p(n) are
related by finite divisor transforms, but have different square-jump data.
Every vector in `closureWithConstants` has equal jumps at p and p².
The valuation has jumps 1 and 2, so any actual Q representative is outside.
This does not assert nonmembership of the logarithmic target.
-/

noncomputable section
namespace RiemannResearch.RH.PrimePowerTarget

open ZetaTwoHilbert SquarefreeRadicalDifference

/-- The number immediately before p² has no factor p. -/
theorem factorization_prime_sq_pred (p : ℕ) (hp : p.Prime) :
    (p ^ 2 - 1).factorization p = 0 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpred : ¬p ∣ p - 1 := by
    intro hd
    have hle := Nat.le_of_dvd (show 0 < p - 1 by omega) hd
    omega
  have hpos : 1 ≤ p ^ 2 := by nlinarith
  have ht : p - 1 + 1 = p := by omega
  have hs : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel hpos
  have hm := congrArg (fun n : ℕ => p * n) ht
  have he : p ^ 2 - 1 = p * (p - 1) + (p - 1) := by nlinarith
  rw [he]
  exact Nat.factorization_eq_zero_of_remainder (p - 1) hpred

/-- A prime valuation cannot belong to the actual squarefree closure,
even after constants are added. The premise identifies an actual Q vector
by all its positive physical coordinates. -/
theorem primeValuation_not_mem_closureWithConstants
    (p : ℕ) (hp : p.Prime) (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n → qSequence x n = (n.factorization p : ℝ)) :
    x ∉ closureWithConstants := by
  intro hx
  have hp2 : 2 ≤ p := hp.two_le
  have hpow : 0 < p ^ 2 := pow_pos hp.pos _
  have hpowpred : 0 < p ^ 2 - 1 := by
    have hge : 2 ≤ p ^ 2 := by nlinarith
    omega
  have hx_p : qSequence x p = 1 := by
    rw [hseq p hp.pos, hp.factorization_self]
    norm_num
  have hx_pred : qSequence x (p - 1) = 0 := by
    rw [hseq (p - 1) (by omega), Nat.factorization_eq_zero_of_lt (by omega)]
    norm_num
  have hx_sq : qSequence x (p ^ 2) = 2 := by
    rw [hseq (p ^ 2) hpow, Nat.factorization_pow_self hp]
    norm_num
  have hx_sq_pred : qSequence x (p ^ 2 - 1) = 0 := by
    rw [hseq (p ^ 2 - 1) hpowpred, factorization_prime_sq_pred p hp]
    norm_num
  have hj := closureWithConstants_difference_pow p 2 hp2 (by decide) x hx
  simp only [qDifference, hx_sq, hx_sq_pred, hx_p, hx_pred] at hj
  norm_num at hj

end RiemannResearch.RH.PrimePowerTarget
