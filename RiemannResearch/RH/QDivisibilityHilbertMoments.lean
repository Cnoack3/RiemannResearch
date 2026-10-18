/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDilationMoments
import RiemannResearch.RH.QDivisibilityDensity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NormNum

/-!
# Actual Q-Hilbert moments of divisibility indicators

Source: the user-requested reflected-vector investigation, 17 October 2026.
The complete inverse-square reindexing is the existing
`inversePowerMean_dvd`; no Haar residue law or finite-tail substitution is used.
These moments support quantitative legal trials for reflected residue vectors.
-/

noncomputable section
namespace RiemannResearch.RH.QDivisibilityDensity
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative

private theorem mean_one :
    inversePowerMean 0 (fun _ : ℕ => (1 : ℝ)) = 1 := by
  have h : inner ℝ qOne qOne = 1 := by
    rw [real_inner_self_eq_norm_sq, qOne_norm_sq]
  rw [qInner_eq_inversePowerMean, qSequence_qOne] at h
  simpa [inversePowerMean, qOneSequence] using h

/-- Exact complete mixed moment, retaining the dilated physical sequence. -/
theorem inner_qDivisor_eq_dilation (f : QHilbert) (d : ℕ) (hd : 0 < d) :
    inner ℝ f (qDivisor d) =
      (1 / (d : ℝ) ^ 2) *
        inversePowerMean 0 (fun n => qSequence f (d * n)) := by
  rw [qInner_eq_inversePowerMean]
  calc
    inversePowerMean 0 (fun n => qSequence f n * qSequence (qDivisor d) n) =
        inversePowerMean 0 (fun n => if d ∣ n then qSequence f n else 0) := by
      unfold inversePowerMean
      apply tsum_congr
      intro n
      simp only [qSequence_qDivisor, positiveDivisor, Nat.succ_ne_zero, ↓reduceIte]
      split_ifs <;> simp
    _ = _ := inversePowerMean_dvd d hd (qSequence f)

/-- The actual Q mass of the positive divisibility event. -/
theorem qOne_inner_qDivisor (d : ℕ) (hd : 0 < d) :
    inner ℝ qOne (qDivisor d) = 1 / (d : ℝ) ^ 2 := by
  rw [inner_qDivisor_eq_dilation qOne d hd]
  have he :
      inversePowerMean 0 (fun n => qSequence qOne (d * n)) =
        inversePowerMean 0 (fun _ : ℕ => (1 : ℝ)) := by
    unfold inversePowerMean
    apply tsum_congr
    intro n
    simp [qSequence_qOne, qOneSequence, Nat.ne_of_gt hd]
  rw [he, mean_one, mul_one]

/-- Exact indicator norm; the entire infinite progression is included. -/
theorem qDivisor_norm_sq (d : ℕ) (hd : 0 < d) :
    ‖qDivisor d‖ ^ 2 = 1 / (d : ℝ) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_qDivisor_eq_dilation (qDivisor d) d hd]
  have he :
      inversePowerMean 0 (fun n => qSequence (qDivisor d) (d * n)) =
        inversePowerMean 0 (fun _ : ℕ => (1 : ℝ)) := by
    unfold inversePowerMean
    apply tsum_congr
    intro n
    simp [qSequence_qDivisor, positiveDivisor, Nat.ne_of_gt hd]
  rw [he, mean_one, mul_one]

/-- Actual overlap, with lcm rather than a false independence assumption. -/
theorem qDivisor_inner_qDivisor (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    inner ℝ (qDivisor d) (qDivisor e) = 1 / (Nat.lcm d e : ℝ) ^ 2 := by
  have h :
      inner ℝ (qDivisor d) (qDivisor e) =
        inner ℝ qOne (qDivisor (Nat.lcm d e)) := by
    rw [qInner_eq_inversePowerMean, qInner_eq_inversePowerMean]
    unfold inversePowerMean
    apply tsum_congr
    intro n
    simp only [qSequence_qDivisor, qSequence_qOne, positiveDivisor,
      qOneSequence, Nat.succ_ne_zero, ↓reduceIte]
    by_cases hd' : d ∣ n + 1 <;> by_cases he' : e ∣ n + 1 <;>
      simp [Nat.lcm_dvd_iff, hd', he']
  rw [h, qOne_inner_qDivisor _ (Nat.lcm_pos hd he)]

/-- Atoms whose conductors divide d vanish exactly on the d progression. -/
theorem qResidue_inner_qDivisor_eq_zero (a d : ℕ) (hd : 0 < d) (had : a ∣ d) :
    inner ℝ (qResidue a) (qDivisor d) = 0 := by
  rw [inner_qDivisor_eq_dilation (qResidue a) d hd]
  have hz (n : ℕ) : qSequence (qResidue a) (d * n) = 0 := by
    rw [qSequence_qResidue]
    simp [residueFraction,
      Nat.mod_eq_zero_of_dvd (dvd_trans had (dvd_mul_right d n))]
  simp [hz, inversePowerMean]

end RiemannResearch.RH.QDivisibilityDensity
