/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Arbitrary signed conductor blocks cannot remove the preceding linear ramp

Source: the user's symbolic CRT/Ramanujan/Pareto continuation, 28 October 2026.
Every conductor above M agrees with n/d through M. Consequently any signed
block has a fixed linear head determined only by its reciprocal slope.
The complete Q norm controls that entire ramp. No sign restriction,
squarefree assumption, or estimate on individual coefficients is needed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QConductorGapEnergy
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative QResidueHeadSpace

/-- Exact physical ramp for an arbitrary signed block beyond a conductor gap. -/
theorem block_sequence_below_gap (s : Finset ℕ) (c : ℕ → ℝ) (M n : ℕ)
    (hgap : ∀ d ∈ s, M < d) (hnM : n ≤ M) :
    qSequence (∑ d ∈ s, c d • qResidue d) n =
      (∑ d ∈ s, c d / (d : ℝ)) * (n : ℝ) := by
  rw [synthesis_sequence, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hnd : n < d := lt_of_le_of_lt hnM (hgap d hd)
  simp only [residueFraction, Nat.mod_eq_of_lt hnd]
  ring

/-- Exact old/new head energy, with the signed mixed term retained. -/
theorem signed_block_head_energy (G : QHilbert) (s : Finset ℕ) (c : ℕ → ℝ)
    (M : ℕ) (hgap : ∀ d ∈ s, M < d) :
    (∑ n ∈ Finset.Icc 1 M,
      positiveQWeight n * (qSequence (G + ∑ d ∈ s, c d • qResidue d) n) ^ 2) =
    (∑ n ∈ Finset.Icc 1 M, positiveQWeight n * (qSequence G n) ^ 2) +
      (2 * (∑ d ∈ s, c d / (d : ℝ)) / zetaTwo) *
        (∑ n ∈ Finset.Icc 1 M, qSequence G n / (n : ℝ)) +
      (M : ℝ) * (∑ d ∈ s, c d / (d : ℝ)) ^ 2 / zetaTwo := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 M,
        (positiveQWeight n * (qSequence G n) ^ 2 +
          (2 * (∑ d ∈ s, c d / (d : ℝ)) / zetaTwo) *
            (qSequence G n / (n : ℝ)) +
          (∑ d ∈ s, c d / (d : ℝ)) ^ 2 / zetaTwo) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := Finset.mem_Icc.mp hn
      have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn'.1
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
      have he : qSequence (G + ∑ d ∈ s, c d • qResidue d) n =
          qSequence G n + (∑ d ∈ s, c d / (d : ℝ)) * (n : ℝ) := by
        change qSequenceLinear (G + ∑ d ∈ s, c d • qResidue d) n = _
        simp only [map_add, Pi.add_apply]
        change qSequence G n + qSequence (∑ d ∈ s, c d • qResidue d) n = _
        rw [block_sequence_below_gap s c M n hgap hn'.2]
      rw [he]
      unfold positiveQWeight
      field_simp [hnR, ne_of_gt zetaTwo_pos]
      <;> ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [Nat.card_Icc]
      <;> ring

/-- Exact signed head energy, before discarding any infinite-tail contribution. -/
theorem ramp_head_energy (f : QHilbert) (A : ℝ) (M : ℕ)
    (hramp : ∀ n, 0 < n → n ≤ M → qSequence f n = A * (n : ℝ)) :
    (∑ n ∈ Finset.Icc 1 M, positiveQWeight n * (qSequence f n) ^ 2) =
      (M : ℝ) * A ^ 2 / zetaTwo := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 M, A ^ 2 / zetaTwo := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := Finset.mem_Icc.mp hn
      have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn'.1
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
      rw [hramp n hnpos hn'.2]
      unfold positiveQWeight
      field_simp [hnR, ne_of_gt zetaTwo_pos]
      <;> ring
    _ = _ := by simp [Nat.card_Icc]; ring

/-- A physical ramp on M sites contributes exactly M A² / ζ(2) to Q energy. -/
theorem ramp_energy_le (f : QHilbert) (A : ℝ) (M : ℕ)
    (hramp : ∀ n, 0 < n → n ≤ M → qSequence f n = A * (n : ℝ)) :
    (M : ℝ) * A ^ 2 / zetaTwo ≤ ‖f‖ ^ 2 := by
  have hsum := (qSequence_square_summable f).sum_le_tsum
    (Finset.Icc 1 M)
    (fun k _ => mul_nonneg (positiveQWeight_nonneg k) (sq_nonneg _))
  rw [ramp_head_energy f A M hramp, ← qNorm_weighted_sq] at hsum
  exact hsum

/-- The ramp bound retains every signed interaction with an arbitrary old vector. -/
theorem block_gap_energy (G : QHilbert) (s : Finset ℕ) (c : ℕ → ℝ)
    (M : ℕ) (hgap : ∀ d ∈ s, M < d) :
    (M : ℝ) * (∑ d ∈ s, c d / (d : ℝ)) ^ 2 ≤
      zetaTwo * (‖G + ∑ d ∈ s, c d • qResidue d‖ + ‖G‖) ^ 2 := by
  let R : QHilbert := ∑ d ∈ s, c d • qResidue d
  have hlow := ramp_energy_le R (∑ d ∈ s, c d / (d : ℝ)) M
    (fun n _ hnM => block_sequence_below_gap s c M n hgap hnM)
  have htri : ‖R‖ ≤ ‖G + R‖ + ‖G‖ := by
    simpa only [add_sub_cancel_left] using norm_sub_le (G + R) G
  have hsq : ‖R‖ ^ 2 ≤ (‖G + R‖ + ‖G‖) ^ 2 := by
    nlinarith [norm_nonneg R, norm_nonneg (G + R), norm_nonneg G]
  have hout := (div_le_iff₀ zetaTwo_pos).mp (hlow.trans hsq)
  simpa only [R, mul_comm zetaTwo] using hout

/-- Any common bound on old and repaired energies imposes an explicit delay budget. -/
theorem block_gap_budget (G : QHilbert) (s : Finset ℕ) (c : ℕ → ℝ)
    (M : ℕ) (hgap : ∀ d ∈ s, M < d) (B C : ℝ)
    (hG : ‖G‖ ≤ B) (hF : ‖G + ∑ d ∈ s, c d • qResidue d‖ ≤ C) :
    (M : ℝ) * (∑ d ∈ s, c d / (d : ℝ)) ^ 2 ≤
      zetaTwo * (C + B) ^ 2 := by
  have h := block_gap_energy G s c M hgap
  have hB : 0 ≤ B := (norm_nonneg G).trans hG
  have hC : 0 ≤ C := (norm_nonneg _).trans hF
  have hs : (‖G + ∑ d ∈ s, c d • qResidue d‖ + ‖G‖) ^ 2 ≤
      (C + B) ^ 2 := by
    nlinarith [norm_nonneg (G + ∑ d ∈ s, c d • qResidue d), norm_nonneg G]
  exact h.trans (mul_le_mul_of_nonneg_left hs zetaTwo_pos.le)

end RiemannResearch.RH.QConductorGapEnergy
