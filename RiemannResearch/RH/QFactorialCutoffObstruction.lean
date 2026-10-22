/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.PrimeFactorialBlockJumps
import RiemannResearch.RH.QPrimePowerTransformRigidity
import RiemannResearch.RH.QSquarefreeJumpDistance
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A compensated Möbius factorial cutoff fails squarefree legality

Source: the user's Möbius/factorial continuation agenda, 21 October 2026.
The literal cutoff D=3 at p=2 has coefficients μ(1)=1, μ(2)=μ(3)=-1.
Its jumps at 6 and 36 differ by minus one. Subtracting any linear slope
changes both jumps equally and therefore cannot repair this obstruction.
The nonmembership result concerns any actual Q-vector with these physical
coordinates; it does not assume or construct such a vector for every slope.
-/

noncomputable section
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability SquarefreeRadicalDifference QSquarefreeJumpDistance
open RiemannResearch.NumberTheory.PrimeFactorialBlockJumps

-- Use the proved jump interface; avoid normalizing concrete large factorials.
attribute [local irreducible] factorialBlock

/-- The actual three-term Möbius factorial cutoff at base two. -/
def factorialCutoffThreeTwo (n : ℕ) : ℤ :=
  factorialBlock 2 1 n - factorialBlock 2 2 n - factorialBlock 2 3 n

private theorem factorization_two_small :
    (2 : ℕ).factorization 2 = 1 ∧
    (3 : ℕ).factorization 2 = 0 ∧
    (6 : ℕ).factorization 2 = 1 ∧
    (12 : ℕ).factorization 2 = 2 ∧
    (18 : ℕ).factorization 2 = 1 ∧
    (36 : ℕ).factorization 2 = 2 := by
  have h2 : (2 : ℕ).factorization 2 = 1 := Nat.prime_two.factorization_self
  have h3 : (3 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)
  have h6 : (6 : ℕ).factorization 2 = 1 := by
    change (2 * 3 : ℕ).factorization 2 = 1
    rw [Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply, h2, h3]
  have h12 : (12 : ℕ).factorization 2 = 2 := by
    change (2 * 6 : ℕ).factorization 2 = 2
    rw [Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply, h2, h6]
  have h18 : (18 : ℕ).factorization 2 = 1 := by
    change (3 * 6 : ℕ).factorization 2 = 1
    rw [Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply, h3, h6]
  have h36 : (36 : ℕ).factorization 2 = 2 := by
    change (6 * 6 : ℕ).factorization 2 = 2
    simp only [Nat.factorization_mul (by decide : (6 : ℕ) ≠ 0)
      (by decide : (6 : ℕ) ≠ 0), Finsupp.add_apply, h6]
  exact ⟨h2, h3, h6, h12, h18, h36⟩

private theorem three_block_sub (a b c a' b' c' : ℤ) :
    (a - b - c) - (a' - b' - c') =
      (a - a') - (b - b') - (c - c') := by ring

private theorem affine_succ_sub (a b β : ℝ) (n : ℕ) :
    (a - β * (n + 1 : ℕ)) - (b - β * (n : ℝ)) = (a - b) - β := by
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem factorialCutoffThreeTwo_jump_six :
    factorialCutoffThreeTwo 6 - factorialCutoffThreeTwo 5 = 0 := by
  obtain ⟨h2, h3, h6, h12, h18, h36⟩ := factorization_two_small
  have h1 : factorialBlock 2 1 6 - factorialBlock 2 1 5 = 1 := by
    calc
      _ = if 1 ∣ 6 then ((6 / 1).factorization 2 : ℤ) else 0 :=
        factorialBlock_sub_pred 2 1 6 (by decide)
      _ = 1 := by simp only [one_dvd, if_true, Nat.div_one, h6, Nat.cast_one]
  have h2b : factorialBlock 2 2 6 - factorialBlock 2 2 5 = 0 := by
    calc
      _ = if 2 ∣ 6 then ((6 / 2).factorization 2 : ℤ) else 0 :=
        factorialBlock_sub_pred 2 2 6 (by decide)
      _ = 0 := by simp only [show 2 ∣ 6 by decide, if_true,
        show 6 / 2 = 3 by decide, h3, Nat.cast_zero]
  have h3b : factorialBlock 2 3 6 - factorialBlock 2 3 5 = 1 := by
    calc
      _ = if 3 ∣ 6 then ((6 / 3).factorization 2 : ℤ) else 0 :=
        factorialBlock_sub_pred 2 3 6 (by decide)
      _ = 1 := by simp only [show 3 ∣ 6 by decide, if_true,
        show 6 / 3 = 2 by decide, h2, Nat.cast_one]
  exact (three_block_sub
    (factorialBlock 2 1 6) (factorialBlock 2 2 6) (factorialBlock 2 3 6)
    (factorialBlock 2 1 5) (factorialBlock 2 2 5) (factorialBlock 2 3 5)).trans
      (congrArg₂ (fun a b : ℤ => a - b)
        (congrArg₂ (fun a b : ℤ => a - b) h1 h2b) h3b)

theorem factorialCutoffThreeTwo_jump_thirtySix :
    factorialCutoffThreeTwo 36 - factorialCutoffThreeTwo 35 = -1 := by
  obtain ⟨h2, h3, h6, h12, h18, h36⟩ := factorization_two_small
  have h1 : factorialBlock 2 1 36 - factorialBlock 2 1 35 = 2 := by
    calc
      _ = if 1 ∣ 36 then ((36 / 1).factorization 2 : ℤ) else 0 :=
        factorialBlock_sub_pred 2 1 36 (by decide)
      _ = 2 := by simp only [one_dvd, if_true, Nat.div_one, h36, Nat.cast_ofNat]
  have h2b : factorialBlock 2 2 36 - factorialBlock 2 2 35 = 1 := by
    calc
      _ = if 2 ∣ 36 then ((36 / 2).factorization 2 : ℤ) else 0 :=
        factorialBlock_sub_pred 2 2 36 (by decide)
      _ = 1 := by simp only [show 2 ∣ 36 by decide, if_true,
        show 36 / 2 = 18 by decide, h18, Nat.cast_one]
  have h3b : factorialBlock 2 3 36 - factorialBlock 2 3 35 = 2 := by
    calc
      _ = if 3 ∣ 36 then ((36 / 3).factorization 2 : ℤ) else 0 :=
        factorialBlock_sub_pred 2 3 36 (by decide)
      _ = 2 := by simp only [show 3 ∣ 36 by decide, if_true,
        show 36 / 3 = 12 by decide, h12, Nat.cast_ofNat]
  exact (three_block_sub
    (factorialBlock 2 1 36) (factorialBlock 2 2 36) (factorialBlock 2 3 36)
    (factorialBlock 2 1 35) (factorialBlock 2 2 35) (factorialBlock 2 3 35)).trans
      (congrArg₂ (fun a b : ℤ => a - b)
        (congrArg₂ (fun a b : ℤ => a - b) h1 h2b) h3b)

def compensatedFactorialCutoffThreeTwo (β : ℝ) (n : ℕ) : ℝ :=
  (factorialCutoffThreeTwo n : ℝ) - β * (n : ℝ)

theorem compensatedFactorialCutoffThreeTwo_jump_six (β : ℝ) :
    compensatedFactorialCutoffThreeTwo β 6 -
      compensatedFactorialCutoffThreeTwo β 5 = -β := by
  have h : (factorialCutoffThreeTwo 6 : ℝ) - (factorialCutoffThreeTwo 5 : ℝ) = 0 := by
    calc
      _ = ((factorialCutoffThreeTwo 6 - factorialCutoffThreeTwo 5 : ℤ) : ℝ) :=
        (Int.cast_sub _ _).symm
      _ = ((0 : ℤ) : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) factorialCutoffThreeTwo_jump_six
      _ = 0 := by simp only [Int.cast_zero]
  exact ((affine_succ_sub (factorialCutoffThreeTwo 6 : ℝ)
    (factorialCutoffThreeTwo 5 : ℝ) β 5).trans
      (congrArg (fun z : ℝ => z - β) h)).trans (zero_sub β)

theorem compensatedFactorialCutoffThreeTwo_jump_thirtySix (β : ℝ) :
    compensatedFactorialCutoffThreeTwo β 36 -
      compensatedFactorialCutoffThreeTwo β 35 = -1 - β := by
  have h : (factorialCutoffThreeTwo 36 : ℝ) - (factorialCutoffThreeTwo 35 : ℝ) = -1 := by
    calc
      _ = ((factorialCutoffThreeTwo 36 - factorialCutoffThreeTwo 35 : ℤ) : ℝ) :=
        (Int.cast_sub _ _).symm
      _ = ((-1 : ℤ) : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) factorialCutoffThreeTwo_jump_thirtySix
      _ = -1 := by simp only [Int.cast_neg, Int.cast_one]
  exact (affine_succ_sub (factorialCutoffThreeTwo 36 : ℝ)
    (factorialCutoffThreeTwo 35 : ℝ) β 35).trans
      (congrArg (fun z : ℝ => z - β) h)

theorem compensatedFactorialCutoffThreeTwo_square_jump
    (β : ℝ) (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n →
      qSequence x n = compensatedFactorialCutoffThreeTwo β n) :
    qDifference x (6 ^ 2) - qDifference x 6 = -1 := by
  have hx6 : qDifference x 6 = -β := by
    calc
      _ = compensatedFactorialCutoffThreeTwo β 6 -
          compensatedFactorialCutoffThreeTwo β 5 :=
        congrArg₂ (fun a b : ℝ => a - b) (hseq 6 (by decide)) (hseq 5 (by decide))
      _ = -β := compensatedFactorialCutoffThreeTwo_jump_six β
  have hx36 : qDifference x (6 ^ 2) = -1 - β := by
    calc
      _ = compensatedFactorialCutoffThreeTwo β 36 -
          compensatedFactorialCutoffThreeTwo β 35 :=
        congrArg₂ (fun a b : ℝ => a - b) (hseq 36 (by decide)) (hseq 35 (by decide))
      _ = -1 - β := compensatedFactorialCutoffThreeTwo_jump_thirtySix β
  exact (congrArg₂ (fun a b : ℝ => a - b) hx36 hx6).trans (by ring)

/-- No choice of linear tail compensation fixes the squarefree jump defect. -/
theorem compensatedFactorialCutoffThreeTwo_not_mem_closureWithConstants
    (β : ℝ) (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n →
      qSequence x n = compensatedFactorialCutoffThreeTwo β n) :
    x ∉ closureWithConstants := by
  intro hx
  have hj := closureWithConstants_difference_pow 6 2 (by decide) (by decide) x hx
  have hzero : qDifference x (6 ^ 2) - qDifference x 6 = 0 := sub_eq_zero.mpr hj
  linarith [compensatedFactorialCutoffThreeTwo_square_jump β x hseq]

/-- Exact complete error energy against the constant-enlarged legal closure.
The full norm-square remainder is retained and the extracted energy is
independent of the slope compensation. -/
theorem compensatedFactorialCutoffThreeTwo_error_energy_exact
    (β : ℝ) (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n →
      qSequence x n = compensatedFactorialCutoffThreeTwo β n)
    (F : QHilbert) (hF : F ∈ closureWithConstants) :
    ‖x - F‖ ^ 2 = 1 / (2582 * zetaTwo) +
      ‖x - F + (1 / (2582 * zetaTwo)) • squareJumpWitness 6‖ ^ 2 := by
  have hFjump := closureWithConstants_difference_pow 6 2
    (by decide) (by decide) F hF
  have he : qDifference (x - F) (6 ^ 2) - qDifference (x - F) 6 = -1 := by
    rw [qDifference_sub, qDifference_sub, hFjump]
    linarith [compensatedFactorialCutoffThreeTwo_square_jump β x hseq]
  have hden : 2 * zetaTwo * (((6 : ℕ) : ℝ) ^ 4 - ((6 : ℕ) : ℝ) + 1) =
      2582 * zetaTwo := by norm_num <;> ring
  rw [squareJump_energy_exact 6 (by decide) (x - F), he, hden]
  simp only [neg_one_sq, neg_div, neg_smul, sub_neg_eq_add]

theorem compensatedFactorialCutoffThreeTwo_error_sq_lower_bound
    (β : ℝ) (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n →
      qSequence x n = compensatedFactorialCutoffThreeTwo β n)
    (F : QHilbert) (hF : F ∈ closureWithConstants) :
    1 / (2582 * zetaTwo) ≤ ‖x - F‖ ^ 2 := by
  rw [compensatedFactorialCutoffThreeTwo_error_energy_exact β x hseq F hF]
  exact le_add_of_nonneg_right (sq_nonneg _)

end RiemannResearch.RH.PrimePowerTarget
