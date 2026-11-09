/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSignedEnergyCertificate
import RiemannResearch.RH.CRTCarryArithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Complete Q energy intervals for finite signed residue experiments

This is a consumer of the existing signed-energy certificate, not a new
analytic tail estimate. The finite head keeps all signed coefficients and
cross terms; coefficient absolute values are used only in the omitted tail.
The interval is for each specified vector, with no uniform-family claim.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QFiniteEnergyIntervals
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QSignedEnergyCertificate

/-- The exact physical head numerator, prior to division by zeta(2). -/
def headNumerator (f : QHilbert) (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1), qSequence f n ^ 2 / (n : ℝ) ^ 2

/-- Only the physical tail requires an amplitude bound. -/
theorem norm_sq_interval_of_tail_bound (f : QHilbert) (K : ℕ) (hK : 0 < K)
    (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ n : ℕ, K < n → |qSequence f n| ≤ A) :
    headNumerator f K / zetaTwo ≤ ‖f‖ ^ 2 ∧
      ‖f‖ ^ 2 ≤ (headNumerator f K + A ^ 2 / (K : ℝ)) / zetaTwo := by
  have hz : qSequence (0 : QHilbert) = 0 := qSequenceLinear.map_zero
  have hlo := energy_difference_lower f 0 K hK 0 le_rfl (by
    intro n hn
    simp only [signedEnergy, hz, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      sub_zero, neg_zero]
    exact sq_nonneg _)
  have hlo' : headNumerator f K ≤ zetaTwo * ‖f‖ ^ 2 := by
    simpa [signedEnergy, hz, headNumerator] using hlo
  have hhi := energy_difference_lower 0 f K hK (A ^ 2) (sq_nonneg A) (by
    intro n hn
    have hs : qSequence f n ^ 2 ≤ A ^ 2 := by
      have hm := mul_self_le_mul_self (abs_nonneg (qSequence f n)) (hb n hn)
      nlinarith only [hm, sq_abs (qSequence f n)]
    simp only [signedEnergy, hz, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      zero_sub]
    exact neg_le_neg hs)
  have hhi' : zetaTwo * ‖f‖ ^ 2 ≤ headNumerator f K + A ^ 2 / (K : ℝ) := by
    simp only [signedEnergy, hz, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      zero_sub, neg_div, Finset.sum_neg_distrib, norm_zero, mul_neg] at hhi
    change -headNumerator f K - A ^ 2 / (K : ℝ) ≤ -(zetaTwo * ‖f‖ ^ 2) at hhi
    linarith only [hhi]
  constructor
  · exact (div_le_iff₀ zetaTwo_pos).mpr (by simpa only [mul_comm] using hlo')
  · exact (le_div_iff₀ zetaTwo_pos).mpr (by simpa only [mul_comm] using hhi')

/-- Equivalent additive error form: no omitted physical tail is dropped. -/
theorem norm_sq_remainder_interval (f : QHilbert) (K : ℕ) (hK : 0 < K)
    (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ n : ℕ, K < n → |qSequence f n| ≤ A) :
    0 ≤ ‖f‖ ^ 2 - headNumerator f K / zetaTwo ∧
      ‖f‖ ^ 2 - headNumerator f K / zetaTwo ≤ A ^ 2 / (zetaTwo * (K : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := norm_sq_interval_of_tail_bound f K hK A hA hb
  have hsplit : (headNumerator f K + A ^ 2 / (K : ℝ)) / zetaTwo =
      headNumerator f K / zetaTwo + A ^ 2 / (zetaTwo * (K : ℝ)) := by
    rw [add_div, div_div, mul_comm (K : ℝ) zetaTwo]
  rw [hsplit] at hhi
  constructor <;> linarith only [hlo, hhi]

theorem qSequence_sum_residues (s : Finset ℕ) (c : ℕ → ℝ) (n : ℕ) :
    qSequence (∑ d ∈ s, c d • qResidue d) n =
      ∑ d ∈ s, c d * residueFraction d n := by
  change qSequenceLinear (∑ d ∈ s, c d • qResidue d) n = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ d ∈ s, c d * qSequence (qResidue d) n) = _
  simp_rw [qSequence_qResidue]

theorem sum_residues_physical_bound (s : Finset ℕ) (c : ℕ → ℝ) (n : ℕ) :
    |qSequence (∑ d ∈ s, c d • qResidue d) n| ≤ ∑ d ∈ s, |c d| := by
  rw [qSequence_sum_residues]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (CRTCarryArithmetic.residueFraction_abs_le_one d n) (abs_nonneg (c d))

/-- A finite sum certificate, retaining every signed term inside each square. -/
theorem sum_residues_norm_sq_interval (s : Finset ℕ) (c : ℕ → ℝ)
    (K : ℕ) (hK : 0 < K) :
    let H : ℝ := (∑ n ∈ Finset.range (K + 1),
      (∑ d ∈ s, c d * residueFraction d n) ^ 2 / (n : ℝ) ^ 2) / zetaTwo
    H ≤ ‖∑ d ∈ s, c d • qResidue d‖ ^ 2 ∧
      ‖∑ d ∈ s, c d • qResidue d‖ ^ 2 ≤
        H + (∑ d ∈ s, |c d|) ^ 2 / (zetaTwo * (K : ℝ)) := by
  have h := norm_sq_remainder_interval (∑ d ∈ s, c d • qResidue d) K hK
    (∑ d ∈ s, |c d|) (Finset.sum_nonneg (fun d _ => abs_nonneg (c d)))
    (fun n _ => sum_residues_physical_bound s c n)
  simp only [headNumerator, qSequence_sum_residues] at h
  dsimp only
  constructor <;> linarith only [h.1, h.2]

end RiemannResearch.RH.QFiniteEnergyIntervals
