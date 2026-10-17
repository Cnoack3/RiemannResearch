/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.QSignedEnergyCertificate
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! # A certified full-Q composite-anchor gain

For the dyadic block (3,6], the squarefree anchors are 5 and 6. The explicit
quarter-step from canonical B_4 to B_5 saves at least 1/(10000*zetaTwo) in
complete Q energy and stays squarefree-legal and exact on 1,...,4.
This is a finite arithmetic provider, not a cofinal power-cost estimate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCompositeSixGain
open ZetaTwoHilbert Pareto ArithmeticCumulative

def oldError (n : ℕ) : ℝ :=
  1 - (n % 2 : ℕ) / 2 - (n % 3 : ℕ) / 3 - (n % 5 : ℕ) / 6

def errorStep (n : ℕ) : ℝ := (((n % 6 : ℕ) : ℝ) - ((n % 5 : ℕ) : ℝ)) / 30

def physicalGain (n : ℕ) : ℝ :=
  oldError n ^ 2 - (oldError n + errorStep n / 4) ^ 2

theorem physicalGain_mod (n : ℕ) : physicalGain n = physicalGain (n % 30) := by
  simp only [physicalGain, oldError, errorStep,
    Nat.mod_mod_of_dvd n (by norm_num : 2 ∣ 30),
    Nat.mod_mod_of_dvd n (by norm_num : 3 ∣ 30),
    Nat.mod_mod_of_dvd n (by norm_num : 5 ∣ 30),
    Nat.mod_mod_of_dvd n (by norm_num : 6 ∣ 30)]

theorem physicalGain_lower (n : ℕ) : -(41 / 900 : ℝ) ≤ physicalGain n := by
  rw [physicalGain_mod]
  have h := Nat.mod_lt n (by norm_num : 0 < 30)
  generalize n % 30 = r at *
  interval_cases r <;> norm_num [physicalGain, oldError, errorStep]

theorem physicalGain_abs (n : ℕ) : |physicalGain n| ≤ 1 := by
  rw [physicalGain_mod]
  have h := Nat.mod_lt n (by norm_num : 0 < 30)
  generalize n % 30 = r at *
  interval_cases r <;> norm_num [physicalGain, oldError, errorStep]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel-checked rational normalization of the complete 240-site prefix.
theorem physicalGain_prefix :
    (3 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.range 241, physicalGain n / (n : ℝ) ^ 2 := by
  norm_num [Finset.sum_range_succ, physicalGain, oldError, errorStep]

theorem oldError_sequence (n : ℕ) (hn : 0 < n) :
    qSequence (qOne - QMobiusExactHead.exactHead 4) n = oldError n := by
  change qSequenceLinear (qOne - QMobiusExactHead.exactHead 4) n = _
  simp only [map_sub]
  change qSequence qOne n - qSequence (QMobiusExactHead.exactHead 4) n = _
  rw [qSequence_qOne, QMobiusExactHead.exactHead_sequence]
  have hm2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by decide)
  have hm3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by decide)
  have hm4 : ArithmeticFunction.moebius 4 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  have hm5 : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by decide)
  norm_num [qOneSequence, Nat.ne_of_gt hn, canonicalMobiusHead, mobiusReciprocalSum,
    Finset.sum_Icc_succ_top, residueFraction, Nat.mod_one, hm2, hm3, hm4, hm5, oldError]
  <;> ring

theorem freshError_sequence (n : ℕ) (hn : 0 < n) :
    qSequence (qOne - QMobiusExactHead.exactHead 5) n = oldError n + errorStep n := by
  change qSequenceLinear (qOne - QMobiusExactHead.exactHead 5) n = _
  simp only [map_sub]
  change qSequence qOne n - qSequence (QMobiusExactHead.exactHead 5) n = _
  rw [qSequence_qOne, QMobiusExactHead.exactHead_sequence]
  have hm2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by decide)
  have hm3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by decide)
  have hm4 : ArithmeticFunction.moebius 4 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  have hm5 : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by decide)
  norm_num [qOneSequence, Nat.ne_of_gt hn, canonicalMobiusHead, mobiusReciprocalSum,
    Finset.sum_Icc_succ_top, residueFraction, Nat.mod_one, hm2, hm3, hm4, hm5,
    oldError, errorStep]
  <;> ring
end RiemannResearch.RH.QCompositeSixGain

namespace RiemannResearch.RH.QCompositeSixGain
open ZetaTwoHilbert ZetaTwoProbability QSignedEnergyCertificate

def trial : QHilbert :=
  (3 / 4 : ℝ) • QMobiusExactHead.exactHead 4 +
    (1 / 4 : ℝ) • QMobiusExactHead.exactHead 5

theorem trial_error_sequence (n : ℕ) (hn : 0 < n) :
    qSequence (qOne - trial) n = oldError n + errorStep n / 4 := by
  have he : qOne - trial =
      (3 / 4 : ℝ) • (qOne - QMobiusExactHead.exactHead 4) +
        (1 / 4 : ℝ) • (qOne - QMobiusExactHead.exactHead 5) := by
    unfold trial
    module
  rw [he]
  change qSequenceLinear (_ + _) n = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (3 / 4 : ℝ) * qSequence (qOne - QMobiusExactHead.exactHead 4) n +
    (1 / 4 : ℝ) * qSequence (qOne - QMobiusExactHead.exactHead 5) n = _
  rw [oldError_sequence n hn, freshError_sequence n hn]
  ring

theorem signedEnergy_eq (n : ℕ) :
    signedEnergy (qOne - QMobiusExactHead.exactHead 4) (qOne - trial) n =
      physicalGain n := by
  by_cases hn : n = 0
  · subst n
    norm_num [signedEnergy, qSequence, physicalGain, oldError, errorStep]
  · rw [signedEnergy, oldError_sequence n (Nat.pos_of_ne_zero hn),
      trial_error_sequence n (Nat.pos_of_ne_zero hn)]
    rfl

theorem old_legal : QMobiusExactHead.exactHead 4 ∈ qSquarefreeCRTSpan := by
  apply QSquarefreeSublinearHeads.exactHead_mem_squarefreeSpan 4
  change Squarefree (5 : ℕ)
  intro d hd
  have hdd : d ∣ 5 := dvd_trans (dvd_mul_right d d) hd
  have hle : d ≤ 5 := Nat.le_of_dvd (by norm_num) hdd
  interval_cases d <;> norm_num at hd <;> norm_num

theorem fresh_legal : QMobiusExactHead.exactHead 5 ∈ qSquarefreeCRTSpan := by
  apply QSquarefreeSublinearHeads.exactHead_mem_squarefreeSpan 5
  change Squarefree (6 : ℕ)
  intro d hd
  have hdd : d ∣ 6 := dvd_trans (dvd_mul_right d d) hd
  have hle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hdd
  interval_cases d <;> norm_num at hd <;> norm_num

theorem trial_legal : trial ∈ qSquarefreeCRTSpan :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ old_legal)
    (Submodule.smul_mem _ _ fresh_legal)

theorem trial_exact (n : ℕ) (hn : 0 < n) (hn4 : n ≤ 4) :
    qSequence trial n = 1 := by
  change qSequenceLinear (_ + _) n = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (3 / 4 : ℝ) * qSequence (QMobiusExactHead.exactHead 4) n +
    (1 / 4 : ℝ) * qSequence (QMobiusExactHead.exactHead 5) n = _
  rw [QMobiusExactHead.exactHead_exact 4 n hn hn4,
    QMobiusExactHead.exactHead_exact 5 n hn (by omega)]
  norm_num

theorem trial_gain_lower :
    (1 / 10000 : ℝ) / zetaTwo ≤
      ‖qOne - QMobiusExactHead.exactHead 4‖ ^ 2 - ‖qOne - trial‖ ^ 2 := by
  have h := energy_difference_lower
    (qOne - QMobiusExactHead.exactHead 4) (qOne - trial) 240 (by norm_num)
    (41 / 900) (by norm_num)
    (by intro n hn; rw [signedEnergy_eq]; exact physicalGain_lower n)
  simp only [signedEnergy_eq] at h
  have hp := physicalGain_prefix
  apply (div_le_iff₀ zetaTwo_pos).mpr
  nlinarith only [h, hp]

def direction : QHilbert :=
  QMobiusExactHead.exactHead 5 - QMobiusExactHead.exactHead 4

def source : ℝ := inner ℝ (qOne - QMobiusExactHead.exactHead 4) direction
def denominator : ℝ := ‖direction‖ ^ 2
def gain : ℝ := source ^ 2 / denominator

theorem line_legal (t : ℝ) :
    QMobiusExactHead.exactHead 4 + t • direction ∈ qSquarefreeCRTSpan :=
  Submodule.add_mem _ old_legal
    (Submodule.smul_mem _ _ (Submodule.sub_mem _ fresh_legal old_legal))

theorem line_exact (t : ℝ) (n : ℕ) (hn : 0 < n) (hn4 : n ≤ 4) :
    qSequence (QMobiusExactHead.exactHead 4 + t • direction) n = 1 := by
  have hd : qSequence direction n = 0 := by
    change qSequenceLinear (QMobiusExactHead.exactHead 5 -
      QMobiusExactHead.exactHead 4) n = 0
    rw [map_sub]
    change qSequence (QMobiusExactHead.exactHead 5) n -
      qSequence (QMobiusExactHead.exactHead 4) n = 0
    rw [QMobiusExactHead.exactHead_exact 5 n hn (by omega),
      QMobiusExactHead.exactHead_exact 4 n hn hn4]
    norm_num
  change qSequenceLinear (_ + _) n = 1
  rw [map_add, map_smul]
  change qSequence (QMobiusExactHead.exactHead 4) n + t * qSequence direction n = 1
  rw [QMobiusExactHead.exactHead_exact 4 n hn hn4, hd]
  ring

theorem denominator_pos : 0 < denominator := by
  have he : direction = (qOne - QMobiusExactHead.exactHead 4) -
      (qOne - QMobiusExactHead.exactHead 5) := by unfold direction; module
  have hv : qSequence direction 5 = -(1 / 6 : ℝ) := by
    rw [he]
    change qSequenceLinear (_ - _) 5 = _
    rw [map_sub]
    change qSequence (qOne - QMobiusExactHead.exactHead 4) 5 -
      qSequence (qOne - QMobiusExactHead.exactHead 5) 5 = _
    rw [oldError_sequence 5 (by norm_num), freshError_sequence 5 (by norm_num)]
    norm_num [oldError, errorStep]
  have hn : direction ≠ 0 := by
    intro hz
    simp [hz, qSequence] at hv
  exact sq_pos_of_pos (norm_pos_iff.mpr hn)

theorem line_completion (t : ℝ) :
    ‖qOne - (QMobiusExactHead.exactHead 4 + t • direction)‖ ^ 2 =
      ‖qOne - QMobiusExactHead.exactHead 4‖ ^ 2 - gain +
        denominator * (t - source / denominator) ^ 2 := by
  have he : qOne - (QMobiusExactHead.exactHead 4 + t • direction) =
      (qOne - QMobiusExactHead.exactHead 4) - t • direction := by module
  rw [he, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    inner_smul_right]
  unfold gain source denominator
  have hd : ‖direction‖ ^ 2 ≠ 0 := ne_of_gt denominator_pos
  have hdn : ‖direction‖ ≠ 0 := by
    intro hz
    exact hd (by rw [hz]; norm_num)
  field_simp [hd, hdn]
  <;> ring

theorem gain_lower : (1 / 10000 : ℝ) / zetaTwo ≤ gain := by
  have h := line_completion (1 / 4)
  have ht : QMobiusExactHead.exactHead 4 + (1 / 4 : ℝ) • direction = trial := by
    unfold trial direction
    module
  rw [ht] at h
  have hn : 0 ≤ denominator * ((1 / 4 : ℝ) - source / denominator) ^ 2 :=
    mul_nonneg denominator_pos.le (sq_nonneg _)
  linarith only [trial_gain_lower, h, hn]
end RiemannResearch.RH.QCompositeSixGain
