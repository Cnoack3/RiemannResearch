/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QConductorEstimates
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Reciprocal multiplication has no uniform inverse on unbounded residue dictionaries

Source: Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf, Corollary 7.2.
These are direct finite corollaries of the existing QConductorEstimates bounds.
QConductorDecay already supplies a normalized sequence witnessing the same
noncoercivity. This module records explicit thresholds and the prime-only
obstruction, without assuming full reciprocal totality or RH.

-/

noncomputable section
namespace RiemannResearch.RH.QReciprocalNoncoercivity
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal

/-- The inverse amplification is at least square root of (d-1)/zeta(2). -/
theorem residue_reciprocal_inverse_amplification (d : ℕ) (hd : 2 ≤ d) :
    (((d : ℝ) - 1) / zetaTwo) * ‖B (qResidue d)‖ ^ 2 ≤
      ‖qResidue d‖ ^ 2 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have hdm : 0 < (d : ℝ) - 1 := by linarith
  have hz := zetaTwo_pos
  have hs := pow_le_pow_left₀ (norm_nonneg _)
    (B_qResidue_norm_le d (by omega)) 2
  calc
    _ ≤ (((d : ℝ) - 1) / zetaTwo) * (1 / (d : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ((d : ℝ) - 1) / (zetaTwo * (d : ℝ) ^ 2) := by ring
    _ ≤ _ := qResidue_norm_sq_ge_head d (by omega)

theorem reciprocal_residue_norm_sq_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < ‖B (qResidue d)‖ ^ 2 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have hdm : 0 < (d : ℝ) - 1 := by linarith
  have hzeta := zetaTwo_pos
  have hq : 0 < ‖qResidue d‖ ^ 2 :=
    (show 0 < ((d : ℝ) - 1) / (zetaTwo * (d : ℝ) ^ 2) by
      positivity).trans_le (qResidue_norm_sq_ge_head d (by omega))
  have hb : B (qResidue d) ≠ 0 := by
    intro hb
    have hz : qResidue d = 0 := B_faithful _ (by rw [hb, inner_zero_right])
    rw [hz, norm_zero] at hq
    norm_num at hq
  exact sq_pos_of_pos (norm_pos_iff.mpr hb)

/-- An explicit conductor threshold defeats any proposed squared inverse constant. -/
theorem residue_exceeds_reciprocal_inverse_constant (d : ℕ) (hd : 2 ≤ d)
    (C : ℝ) (hC : zetaTwo * C + 1 < (d : ℝ)) :
    C * ‖B (qResidue d)‖ ^ 2 < ‖qResidue d‖ ^ 2 := by
  have hc : C < ((d : ℝ) - 1) / zetaTwo :=
    (lt_div_iff₀ zetaTwo_pos).mpr (by nlinarith)
  exact (mul_lt_mul_of_pos_right hc (reciprocal_residue_norm_sq_pos d hd)).trans_le
    (residue_reciprocal_inverse_amplification d hd)

/-- The obstruction already occurs among prime conductors. -/
theorem exists_prime_exceeding_reciprocal_inverse_constant (C : ℝ) :
    ∃ p : ℕ, p.Prime ∧ C * ‖B (qResidue p)‖ ^ 2 < ‖qResidue p‖ ^ 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (zetaTwo * C + 1)
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
  exact ⟨p, hp, residue_exceeds_reciprocal_inverse_constant p hp.two_le C
    (hn.trans_le (by exact_mod_cast hnp))⟩

/-- Every unbounded conductor dictionary has the same reciprocal instability. -/
theorem exists_dictionary_atom_exceeding_reciprocal_inverse_constant
    (D : Set ℕ) (hD : ∀ N : ℕ, ∃ d ∈ D, N ≤ d) (C : ℝ) :
    ∃ d ∈ D, 2 ≤ d ∧ C * ‖B (qResidue d)‖ ^ 2 < ‖qResidue d‖ ^ 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (zetaTwo * C + 1)
  obtain ⟨d, hdD, hnd⟩ := hD (max 2 n)
  have hd : 2 ≤ d := (le_max_left 2 n).trans hnd
  have hnd' : n ≤ d := (le_max_right 2 n).trans hnd
  exact ⟨d, hdD, hd, residue_exceeds_reciprocal_inverse_constant d hd C
    (hn.trans_le (by exact_mod_cast hnd'))⟩

/-- There is no uniform inverse estimate even on the individual prime atoms. -/
theorem no_uniform_reciprocal_inverse_on_prime_atoms :
    ¬ ∃ C : ℝ, ∀ p : ℕ, p.Prime → ‖qResidue p‖ ≤ C * ‖B (qResidue p)‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨p, hp, hbad⟩ := exists_prime_exceeding_reciprocal_inverse_constant (C ^ 2)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) (hC p hp) 2
  rw [mul_pow] at hsq
  exact (not_le_of_gt hbad) hsq

/-- No space containing an unbounded residue dictionary has a bounded reciprocal inverse. -/
theorem no_uniform_reciprocal_inverse_on_dictionary_space
    (S : Set QHilbert) (D : Set ℕ)
    (hD : ∀ N : ℕ, ∃ d ∈ D, N ≤ d) (hmem : ∀ d ∈ D, qResidue d ∈ S) :
    ¬ ∃ C : ℝ, ∀ f ∈ S, ‖f‖ ≤ C * ‖B f‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨d, hdD, _hd, hbad⟩ :=
    exists_dictionary_atom_exceeding_reciprocal_inverse_constant D hD (C ^ 2)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) (hC _ (hmem d hdD)) 2
  rw [mul_pow] at hsq
  exact (not_le_of_gt hbad) hsq

end RiemannResearch.RH.QReciprocalNoncoercivity
