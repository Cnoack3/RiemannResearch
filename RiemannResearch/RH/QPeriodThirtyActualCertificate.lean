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
# Actual complete-Q norm certificate for a period-thirty legal trial

The rational trial is g₂+g₃+(4/5)g₅−(1/5)g₆+(1/5)g₁₅+(1/5)g₃₀.
Its complete squared Q error is less than 27/1000, improving the requested 1/32
bound. Two complete periods and all remaining progression tails are retained.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPeriodThirtyActualCertificate
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative

def trialThirty : QHilbert :=
  qResidue 2 + qResidue 3 + (4 / 5 : ℝ) • qResidue 5 -
    (1 / 5 : ℝ) • qResidue 6 + (1 / 5 : ℝ) • qResidue 15 +
    (1 / 5 : ℝ) • qResidue 30

def trialThirtyValue (n : ℕ) : ℝ :=
  residueFraction 2 n + residueFraction 3 n + (4 / 5 : ℝ) * residueFraction 5 n -
    (1 / 5 : ℝ) * residueFraction 6 n + (1 / 5 : ℝ) * residueFraction 15 n +
    (1 / 5 : ℝ) * residueFraction 30 n

theorem trialThirty_mem_legal : trialThirty ∈ ZetaTwoOptimizerStage.closure := by
  have sf2 : Squarefree (2 : ℕ) := Nat.prime_two.squarefree
  have sf3 : Squarefree (3 : ℕ) := (by norm_num : Nat.Prime 3).squarefree
  have sf6 : Squarefree (6 : ℕ) :=
    (Nat.squarefree_mul (by decide : Nat.Coprime 2 3)).mpr ⟨sf2, sf3⟩
  have sf5 : Squarefree (5 : ℕ) := (by norm_num : Nat.Prime 5).squarefree
  have sf15 : Squarefree (15 : ℕ) :=
    (Nat.squarefree_mul (by decide : Nat.Coprime 3 5)).mpr ⟨sf3, sf5⟩
  have sf30 : Squarefree (30 : ℕ) :=
    (Nat.squarefree_mul (by decide : Nat.Coprime 2 15)).mpr ⟨sf2, sf15⟩
  have h2 : qResidue 2 ∈ ZetaTwoOptimizerStage.closure :=
    QSquarefreeDimension.qResidue_mem_of_squarefree (by norm_num) sf2
  have h3 : qResidue 3 ∈ ZetaTwoOptimizerStage.closure :=
    QSquarefreeDimension.qResidue_mem_of_squarefree (by norm_num) sf3
  have h5 : qResidue 5 ∈ ZetaTwoOptimizerStage.closure :=
    QSquarefreeDimension.qResidue_mem_of_squarefree (by norm_num) sf5
  have h6 : qResidue 6 ∈ ZetaTwoOptimizerStage.closure :=
    QSquarefreeDimension.qResidue_mem_of_squarefree (by norm_num) sf6
  have h15 : qResidue 15 ∈ ZetaTwoOptimizerStage.closure :=
    QSquarefreeDimension.qResidue_mem_of_squarefree (by norm_num) sf15
  have h30 : qResidue 30 ∈ ZetaTwoOptimizerStage.closure :=
    QSquarefreeDimension.qResidue_mem_of_squarefree (by norm_num) sf30
  unfold trialThirty
  exact ZetaTwoOptimizerStage.closure.add_mem
    (ZetaTwoOptimizerStage.closure.add_mem
      (ZetaTwoOptimizerStage.closure.sub_mem
        (ZetaTwoOptimizerStage.closure.add_mem
          (ZetaTwoOptimizerStage.closure.add_mem h2 h3)
          (ZetaTwoOptimizerStage.closure.smul_mem _ h5))
        (ZetaTwoOptimizerStage.closure.smul_mem _ h6))
      (ZetaTwoOptimizerStage.closure.smul_mem _ h15))
    (ZetaTwoOptimizerStage.closure.smul_mem _ h30)

theorem trialThirty_sequence (n : ℕ) : qSequence trialThirty n = trialThirtyValue n := by
  change qSequenceLinear (qResidue 2 + qResidue 3 + (4 / 5 : ℝ) • qResidue 5 -
    (1 / 5 : ℝ) • qResidue 6 + (1 / 5 : ℝ) • qResidue 15 +
    (1 / 5 : ℝ) • qResidue 30) n = _
  simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change qSequence (qResidue 2) n + qSequence (qResidue 3) n +
    (4 / 5 : ℝ) * qSequence (qResidue 5) n - (1 / 5 : ℝ) * qSequence (qResidue 6) n +
    (1 / 5 : ℝ) * qSequence (qResidue 15) n + (1 / 5 : ℝ) * qSequence (qResidue 30) n = _
  simp only [qSequence_qResidue, trialThirtyValue]

theorem trialThirty_bounded (n : ℕ) : |qSequence trialThirty n| ≤ (4 : ℝ) := by
  rw [trialThirty_sequence]
  unfold trialThirtyValue residueFraction
  have h2 : ((n % 2 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (Nat.mod_lt n (by decide : 0 < 2)).le
  have h3 : ((n % 3 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (Nat.mod_lt n (by decide : 0 < 3)).le
  have h5 : ((n % 5 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (Nat.mod_lt n (by decide : 0 < 5)).le
  have h6 : ((n % 6 : ℕ) : ℝ) ≤ 6 := by exact_mod_cast (Nat.mod_lt n (by decide : 0 < 6)).le
  have h15 : ((n % 15 : ℕ) : ℝ) ≤ 15 := by exact_mod_cast (Nat.mod_lt n (by decide : 0 < 15)).le
  have h30 : ((n % 30 : ℕ) : ℝ) ≤ 30 := by exact_mod_cast (Nat.mod_lt n (by decide : 0 < 30)).le
  apply abs_le.mpr
  constructor <;> norm_num <;>
    nlinarith [Nat.cast_nonneg (α := ℝ) (n % 2), Nat.cast_nonneg (α := ℝ) (n % 3),
      Nat.cast_nonneg (α := ℝ) (n % 5), Nat.cast_nonneg (α := ℝ) (n % 6),
      Nat.cast_nonneg (α := ℝ) (n % 15), Nat.cast_nonneg (α := ℝ) (n % 30)]

theorem trialThirty_periodic (n : ℕ) :
    qSequence trialThirty (n + 30) = qSequence trialThirty n := by
  rw [trialThirty_sequence, trialThirty_sequence]
  have h2 : (n + 30) % 2 = n % 2 := by omega
  have h3 : (n + 30) % 3 = n % 3 := by omega
  have h5 : (n + 30) % 5 = n % 5 := by omega
  have h6 : (n + 30) % 6 = n % 6 := by omega
  have h15 : (n + 30) % 15 = n % 15 := by omega
  have h30 : (n + 30) % 30 = n % 30 := by omega
  simp only [trialThirtyValue, residueFraction, h2, h3, h5, h6, h15, h30]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem trialThirty_error_lt_twenty_seven_thousandths :
    ‖qOne - trialThirty‖ ^ 2 < (27 / 1000 : ℝ) := by
  let U : ℝ := ∑ a : Fin 30, (1 - trialThirtyValue (a.val + 1)) ^ 2 *
    (1 / ((a.val : ℝ) + 1) ^ 2 + 1 / ((a.val : ℝ) + 1 + (30 : ℝ)) ^ 2 +
      1 / ((30 : ℝ) * ((a.val : ℝ) + 1 + (30 : ℝ))))
  have hbound := periodic_qError_two_head_upper 30 (by decide) trialThirty
    (C := 4) trialThirty_bounded trialThirty_periodic
  simp_rw [trialThirty_sequence] at hbound
  change ‖qOne - trialThirty‖ ^ 2 ≤ U / zetaTwo at hbound
  have hnum : U < (87 / 2000 : ℝ) := by
    norm_num [U, Fin.sum_univ_succ, trialThirtyValue, residueFraction]
  have hz := zetaTwo_gt_twenty_nine_eighteenths
  have hlt : U / zetaTwo < (27 / 1000 : ℝ) := by
    apply (div_lt_iff₀ zetaTwo_pos).2
    nlinarith
  exact hbound.trans_lt hlt

theorem trialThirty_error_lt_one_thirtysecond :
    ‖qOne - trialThirty‖ ^ 2 < (1 / 32 : ℝ) :=
  trialThirty_error_lt_twenty_seven_thousandths.trans (by norm_num)

end RiemannResearch.RH.QPeriodThirtyActualCertificate
