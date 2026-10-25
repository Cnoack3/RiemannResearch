/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QPhysicalTailEnergy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A common leading vector for smoothed residue atoms

Source: user-provided measure-change regularity research agenda, A4;
elementary division with remainder and the complete Q-tail estimate.

For every positive conductor d, d B g_d is the same bounded vector
t(n) = n/(n+1), up to a uniformly bounded error supported on n >= d.
This gives a quantitative rank-one expansion of any signed forcing vector.
No squarefree closure, RH, or bound for the inverse Gram matrix is assumed.
-/

noncomputable section
namespace RiemannResearch.RH.QSmoothedResidueAsymptotic
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QAnnihilatorTailEscape QFiniteSupportDualCriterion ArithmeticCumulative

private theorem sequence_sub (f g : QHilbert) (k : ℕ) :
    qSequence (f - g) k = qSequence f k - qSequence g k := by
  exact congrFun (qSequenceLinear.map_sub f g) k

private theorem sequence_smul (c : ℝ) (f : QHilbert) (k : ℕ) :
    qSequence (c • f) k = c * qSequence f k := by
  exact congrFun (qSequenceLinear.map_smul c f) k

def leading : QHilbert := qOne - B qOne

def atomError (d : ℕ) : QHilbert := (d : ℝ) • B (qResidue d) - leading

theorem leading_sequence (k : ℕ) :
    qSequence leading k = (k : ℝ) / ((k : ℝ) + 1) := by
  by_cases hk : k = 0
  · simp [hk]
  rw [leading, sequence_sub, qSequence_B, qSequence_qOne]
  simp only [qOneSequence, if_neg hk]
  field_simp [show (k : ℝ) + 1 ≠ 0 by positivity]
  ring

/-- The exact signed error, including its entire physical tail. -/
theorem atomError_sequence (d k : ℕ) (hd : 0 < d) :
    qSequence (atomError d) k =
      -((d : ℝ) * ((k / d : ℕ) : ℝ)) / ((k : ℝ) + 1) := by
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hkne : (k : ℝ) + 1 ≠ 0 := by positivity
  have he : ((k % d : ℕ) : ℝ) + (d : ℝ) * ((k / d : ℕ) : ℝ) = k := by
    exact_mod_cast Nat.mod_add_div k d
  have hnum : ((k % d : ℕ) : ℝ) - (k : ℝ) =
      -((d : ℝ) * ((k / d : ℕ) : ℝ)) := by linarith
  rw [atomError, sequence_sub, sequence_smul, qSequence_B,
    qSequence_qResidue, leading_sequence]
  unfold residueFraction
  calc
    (d : ℝ) * (((k % d : ℕ) : ℝ) / d / ((k : ℝ) + 1)) -
        (k : ℝ) / ((k : ℝ) + 1) =
      (((k % d : ℕ) : ℝ) - k) / ((k : ℝ) + 1) := by
        field_simp [hdne, hkne]
    _ = _ := by rw [hnum]

theorem atomError_sequence_eq_zero (d k : ℕ) (hd : 0 < d) (hk : k < d) :
    qSequence (atomError d) k = 0 := by
  rw [atomError_sequence d k hd, Nat.div_eq_of_lt hk]
  simp

theorem atomError_sequence_abs_le_one (d k : ℕ) (hd : 0 < d) :
    |qSequence (atomError d) k| ≤ 1 := by
  rw [atomError_sequence d k hd, abs_div, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ (d : ℝ) * ((k / d : ℕ) : ℝ)),
    abs_of_pos (by positivity : 0 < (k : ℝ) + 1)]
  apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
  have hdiv : (d : ℝ) * ((k / d : ℕ) : ℝ) ≤ k := by
    have hn : d * (k / d) ≤ k := by
      have h := Nat.mod_add_div k d
      omega
    exact_mod_cast hn
  linarith

theorem atomError_tail (d : ℕ) (hd : 0 < d) :
    tail (d - 1) (atomError d) = atomError d := by
  apply lp.ext
  funext n
  change atomError d n - finiteHead (d - 1) (atomError d) n = atomError d n
  by_cases hn : n < d - 1
  · rw [finiteHead_apply_of_lt _ _ _ hn]
    have hz := atomError_sequence_eq_zero d (n + 1) hd (by omega)
    have hzn : atomError d n = 0 := by
      have hne : Real.sqrt (qWeight n) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n))
      simpa only [qSequence_succ, div_eq_zero_iff, hne, or_false] using hz
    rw [hzn]
    ring
  · rw [finiteHead_apply_eq_zero _ _ _ (by omega), sub_zero]

/-- Retaining the exact denominator improves the physical bound. -/
theorem atomError_sequence_abs_le_ratio (d k : ℕ) (hd : 0 < d) :
    |qSequence (atomError d) k| ≤ (k : ℝ) / ((k : ℝ) + 1) := by
  rw [atomError_sequence d k hd, abs_div, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ (d : ℝ) * ((k / d : ℕ) : ℝ)),
    abs_of_pos (by positivity : 0 < (k : ℝ) + 1)]
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < (k : ℝ) + 1)).mpr
  have hn : d * (k / d) ≤ k := by
    have h := Nat.mod_add_div k d
    omega
  exact_mod_cast hn

/-- The exact denominator yields a Pareto majorant with constant one. -/
theorem atomError_weighted_square_le (d k : ℕ) (hd : 0 < d) (hk : 0 < k) :
    zetaTwo * (positiveQWeight k * qSequence (atomError d) k ^ 2) ≤
      Pareto.positiveWeight k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hs : qSequence (atomError d) k ^ 2 ≤
      ((k : ℝ) / ((k : ℝ) + 1)) ^ 2 := by
    have ht := mul_self_le_mul_self
      (abs_nonneg (qSequence (atomError d) k))
      (atomError_sequence_abs_le_ratio d k hd)
    nlinarith [sq_abs (qSequence (atomError d) k)]
  have hw : zetaTwo * positiveQWeight k = 1 / (k : ℝ) ^ 2 := by
    unfold positiveQWeight
    field_simp [ne_of_gt zetaTwo_pos, ne_of_gt hkR]
  calc
    _ = (1 / (k : ℝ) ^ 2) * qSequence (atomError d) k ^ 2 := by
      rw [← mul_assoc, hw]
    _ ≤ (1 / (k : ℝ) ^ 2) * ((k : ℝ) / ((k : ℝ) + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 1 / ((k : ℝ) + 1) ^ 2 := by
      field_simp [ne_of_gt hkR, ne_of_gt hk1]
    _ ≤ Pareto.positiveWeight k := by
      unfold Pareto.positiveWeight
      apply one_div_le_one_div_of_le (by positivity : 0 < (k : ℝ) * ((k : ℝ) + 1))
      nlinarith

/-- Complete-tail estimate improved from 2/d to 1/d. -/
theorem atomError_energy_le (d : ℕ) (hd : 0 < d) :
    zetaTwo * ‖atomError d‖ ^ 2 ≤ 1 / (d : ℝ) := by
  have hq : Summable (fun k : ℕ =>
      positiveQWeight (k + d) * qSequence (atomError d) (k + d) ^ 2) :=
    (summable_nat_add_iff
      (f := fun k : ℕ => positiveQWeight k * qSequence (atomError d) k ^ 2) d).mpr
      (qSequence_square_summable (atomError d))
  have hp : Summable (fun k : ℕ => Pareto.positiveWeight (k + d)) :=
    (summable_nat_add_iff (f := Pareto.positiveWeight) d).mpr
      Pareto.positiveWeight_summable
  have hb (k : ℕ) := atomError_weighted_square_le d (k + d) hd (by omega)
  have h := (hq.mul_left zetaTwo).tsum_le_tsum hb hp
  rw [tsum_mul_left, Pareto.positiveWeight_tail_tsum d hd] at h
  have ht : ‖atomError d‖ ^ 2 = ∑' k : ℕ,
      positiveQWeight (k + d) * qSequence (atomError d) (k + d) ^ 2 := by
    have ht := tail_energy_physical (d - 1) (atomError d)
    rw [atomError_tail d hd] at ht
    simpa only [Nat.add_assoc, Nat.sub_add_cancel (show 1 ≤ d by omega)] using ht
  rw [ht]
  exact h


theorem signed_forcing_expansion (r : QHilbert) (d : ℕ) :
    (d : ℝ) * inner ℝ r (B (qResidue d)) - inner ℝ r leading =
      inner ℝ r (atomError d) := by
  rw [atomError, inner_sub_right, inner_smul_right]

/-- A rank-one leading forcing and a conductor-decaying squared remainder. -/
theorem signed_forcing_sq_bound (r : QHilbert) (d : ℕ) (hd : 0 < d) :
    zetaTwo * (d : ℝ) *
      ((d : ℝ) * inner ℝ r (B (qResidue d)) - inner ℝ r leading) ^ 2 ≤
      ‖r‖ ^ 2 := by
  have habs := abs_real_inner_le_norm r (atomError d)
  have hs := mul_self_le_mul_self (abs_nonneg (inner ℝ r (atomError d))) habs
  have hsq : (inner ℝ r (atomError d)) ^ 2 ≤ ‖r‖ ^ 2 * ‖atomError d‖ ^ 2 := by
    nlinarith [sq_abs (inner ℝ r (atomError d))]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he := (le_div_iff₀ hdR).mp (atomError_energy_le d hd)
  rw [signed_forcing_expansion]
  calc
    zetaTwo * (d : ℝ) * (inner ℝ r (atomError d)) ^ 2 ≤
        zetaTwo * (d : ℝ) * (‖r‖ ^ 2 * ‖atomError d‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg zetaTwo_pos.le hdR.le)
    _ = ‖r‖ ^ 2 * ((zetaTwo * ‖atomError d‖ ^ 2) * (d : ℝ)) := by ring
    _ ≤ ‖r‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = ‖r‖ ^ 2 := by ring

theorem inner_atomError_eq_tail (r : QHilbert) (d : ℕ) (hd : 0 < d) :
    inner ℝ r (atomError d) = inner ℝ (tail (d - 1) r) (atomError d) := by
  have hz := inner_finiteHead_tail (d - 1) r (atomError d)
  change inner ℝ (finiteHead (d - 1) r) (tail (d - 1) (atomError d)) = 0 at hz
  rw [atomError_tail d hd] at hz
  rw [tail, inner_sub_left, hz, sub_zero]

/-- The forcing sees only the complete residual tail beyond the conductor.
The exact Pareto majorant gives constant one. -/
theorem signed_forcing_tail_sq_bound (r : QHilbert) (d : ℕ) (hd : 0 < d) :
    zetaTwo * (d : ℝ) *
      ((d : ℝ) * inner ℝ r (B (qResidue d)) - inner ℝ r leading) ^ 2 ≤
      ‖tail (d - 1) r‖ ^ 2 := by
  have habs := abs_real_inner_le_norm (tail (d - 1) r) (atomError d)
  have hs := mul_self_le_mul_self
    (abs_nonneg (inner ℝ (tail (d - 1) r) (atomError d))) habs
  have hsq : (inner ℝ (tail (d - 1) r) (atomError d)) ^ 2 ≤
      ‖tail (d - 1) r‖ ^ 2 * ‖atomError d‖ ^ 2 := by
    nlinarith [sq_abs (inner ℝ (tail (d - 1) r) (atomError d))]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he := (le_div_iff₀ hdR).mp (atomError_energy_le d hd)
  rw [signed_forcing_expansion, inner_atomError_eq_tail r d hd]
  calc
    zetaTwo * (d : ℝ) *
        (inner ℝ (tail (d - 1) r) (atomError d)) ^ 2 ≤
      zetaTwo * (d : ℝ) *
        (‖tail (d - 1) r‖ ^ 2 * ‖atomError d‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg zetaTwo_pos.le hdR.le)
    _ = ‖tail (d - 1) r‖ ^ 2 *
        ((zetaTwo * ‖atomError d‖ ^ 2) * (d : ℝ)) := by ring
    _ ≤ ‖tail (d - 1) r‖ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = ‖tail (d - 1) r‖ ^ 2 := by ring


end RiemannResearch.RH.QSmoothedResidueAsymptotic
