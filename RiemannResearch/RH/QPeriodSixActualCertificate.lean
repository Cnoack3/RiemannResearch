/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPeriodicRationalTail
import RiemannResearch.RH.ZetaTwoElementaryRationalBounds
import RiemannResearch.RH.QSquarefreeDimension
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Actual complete-Q norm certificate for a period-six legal trial

This specializes the complete arithmetic-progression tail estimate to
g₂+g₃+(2/3)g₆. Every infinite tail and the actual zeta normalization is included.
The rational trial was found computationally; the bound uses exact arithmetic.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPeriodSixActualCertificate
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative

def trialSix : QHilbert := qResidue 2 + qResidue 3 + (2 / 3 : ℝ) • qResidue 6

theorem trialSix_mem_legal : trialSix ∈ ZetaTwoOptimizerStage.closure := by
  have sf2 : Squarefree (2 : ℕ) := Nat.prime_two.squarefree
  have sf3 : Squarefree (3 : ℕ) := (by norm_num : Nat.Prime 3).squarefree
  have sf6 : Squarefree (6 : ℕ) :=
    (Nat.squarefree_mul (by decide : Nat.Coprime 2 3)).mpr ⟨sf2, sf3⟩
  unfold trialSix
  apply ZetaTwoOptimizerStage.closure.add_mem
  · apply ZetaTwoOptimizerStage.closure.add_mem
    · exact QSquarefreeDimension.qResidue_mem_of_squarefree (by norm_num) sf2
    · exact QSquarefreeDimension.qResidue_mem_of_squarefree (by norm_num) sf3
  · apply ZetaTwoOptimizerStage.closure.smul_mem
    exact QSquarefreeDimension.qResidue_mem_of_squarefree (by norm_num) sf6

theorem trialSix_sequence (n : ℕ) :
    qSequence trialSix n = residueFraction 2 n + residueFraction 3 n +
      (2 / 3 : ℝ) * residueFraction 6 n := by
  change qSequenceLinear (qResidue 2 + qResidue 3 + (2 / 3 : ℝ) • qResidue 6) n = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change qSequence (qResidue 2) n + qSequence (qResidue 3) n +
    (2 / 3 : ℝ) * qSequence (qResidue 6) n = _
  rw [qSequence_qResidue, qSequence_qResidue, qSequence_qResidue]

theorem trialSix_bounded (n : ℕ) : |qSequence trialSix n| ≤ (3 : ℝ) := by
  rw [trialSix_sequence]
  unfold residueFraction
  have h2 : ((n % 2 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (Nat.mod_lt n (by decide : 0 < 2)).le
  have h3 : ((n % 3 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (Nat.mod_lt n (by decide : 0 < 3)).le
  have h6 : ((n % 6 : ℕ) : ℝ) ≤ 6 := by exact_mod_cast (Nat.mod_lt n (by decide : 0 < 6)).le
  rw [abs_of_nonneg (by positivity)]
  norm_num
  linarith

theorem trialSix_periodic (n : ℕ) : qSequence trialSix (n + 6) = qSequence trialSix n := by
  rw [trialSix_sequence, trialSix_sequence]
  have h2 : (n + 6) % 2 = n % 2 := by omega
  have h3 : (n + 6) % 3 = n % 3 := by omega
  have h6 : (n + 6) % 6 = n % 6 := by omega
  simp only [residueFraction, h2, h3, h6]

/-- An unconditional complete Hilbert-norm estimate, not merely a rational
head computation or a conditional series consumer. -/
theorem trialSix_error_lt_one_sixteenth : ‖qOne - trialSix‖ ^ 2 < (1 / 16 : ℝ) := by
  have hbound := periodic_qError_two_head_upper 6 (by decide) trialSix
    (C := 3) trialSix_bounded trialSix_periodic
  simp_rw [trialSix_sequence] at hbound
  norm_num [Fin.sum_univ_succ, residueFraction] at hbound
  have hz := zetaTwo_gt_twenty_nine_eighteenths
  have hlt : ((669398713 : ℝ) / 6915585600) / zetaTwo < (1 / 16 : ℝ) := by
    apply (div_lt_iff₀ zetaTwo_pos).2
    nlinarith
  exact hbound.trans_lt hlt

end RiemannResearch.RH.QPeriodSixActualCertificate
