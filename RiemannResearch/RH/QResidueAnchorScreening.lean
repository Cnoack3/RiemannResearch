/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QConductorEstimates
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Changing residue anchors before orthogonal screening

Source: independently developed from the user-provided capacity-increment
agenda, 29 October 2026, Priority A. The concrete consumers are
QCRTPrimeInnovation and QCRTInnovationBlock. All norms are complete Q norms.
The raw lower bound and the short-anchor upper bound are arithmetic estimates;
neither supplies an upper bound on the inverse Gram action.
-/

noncomputable section
namespace RiemannResearch.RH.QResidueAnchorScreening
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets QResidueHeadSpace

theorem compensated_anchor_change (m L r : ℕ) (hL : 0 < L) :
    compensatedResidue m L - compensatedResidue m r =
      (-((L : ℝ) / m)) • compensatedResidue L r := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have hc : (L : ℝ) / m * ((r : ℝ) / L) = (r : ℝ) / m := by
    field_simp
  simp only [compensatedResidue, smul_sub, smul_smul, neg_mul, hc, neg_smul]
  abel

theorem anchor_change_mem (s : Finset ℕ) (H L r m : ℕ)
    (hL : L ∈ s) (hr : r ∈ s) (hHL : H < L) (hHr : H < r) :
    compensatedResidue m L - compensatedResidue m r ∈ dictionary s ⊓ headNull H := by
  rw [compensated_anchor_change m L r (by omega)]
  apply Submodule.smul_mem
  refine ⟨?_, ?_⟩
  · exact (dictionary s).sub_mem (Submodule.subset_span ⟨⟨L, hL⟩, rfl⟩)
      ((dictionary s).smul_mem _ (Submodule.subset_span ⟨⟨r, hr⟩, rfl⟩))
  · intro k hk hkH
    exact compensatedResidue_head L r k (by omega) (by omega) (by omega) (by omega)

theorem qResidue_inner_nonneg (m r : ℕ) :
    0 ≤ inner ℝ (qResidue m) (qResidue r) := by
  rw [qInner_weighted]
  apply tsum_nonneg
  intro k
  exact mul_nonneg
    (mul_nonneg (positiveQWeight_nonneg k) (qResidue_physical_nonneg m k))
    (qResidue_physical_nonneg r k)

theorem compensated_energy_upper (m r : ℕ) (hm : 2 ≤ m) (hr : 2 ≤ r) :
    ‖compensatedResidue m r‖ ^ 2 ≤
      2 / (zetaTwo * (m : ℝ)) + 2 * r / (zetaTwo * (m : ℝ) ^ 2) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hu := qResidue_norm_sq_le_two_div m hm
  have hv := mul_le_mul_of_nonneg_left (qResidue_norm_sq_le_two_div r hr)
    (sq_nonneg ((r : ℝ) / m))
  have he : ((r : ℝ) / m) ^ 2 * (2 / (zetaTwo * (r : ℝ))) =
      2 * r / (zetaTwo * (m : ℝ) ^ 2) := by field_simp
  rw [he] at hv
  have hi := mul_nonneg (div_nonneg hrR.le hmR.le) (qResidue_inner_nonneg m r)
  rw [compensatedResidue, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, inner_smul_right]
  nlinarith

theorem raw_energy_lower (m L : ℕ) (hm : 2 ≤ m) (hL : 2 ≤ L) :
    ((L : ℝ) - 8 * m) / (4 * zetaTwo * (m : ℝ) ^ 2) ≤
      ‖compensatedResidue m L‖ ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hLR : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hlo := mul_le_mul_of_nonneg_left (qResidue_norm_sq_ge_half_div L hL)
    (sq_nonneg ((L : ℝ) / m))
  have halg : ((L : ℝ) / m) ^ 2 * (1 / (2 * zetaTwo * (L : ℝ))) =
      L / (2 * zetaTwo * (m : ℝ) ^ 2) := by field_simp
  rw [halg] at hlo
  have hu := qResidue_norm_sq_le_two_div m hm
  have ht := norm_sub_le (qResidue m) (compensatedResidue m L)
  have heq : qResidue m - compensatedResidue m L = ((L : ℝ) / m) • qResidue L := by
    unfold compensatedResidue
    abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hLR hmR)] at ht
  have hs : ((L : ℝ) / m) ^ 2 * ‖qResidue L‖ ^ 2 ≤
      2 * ‖qResidue m‖ ^ 2 + 2 * ‖compensatedResidue m L‖ ^ 2 := by
    have hsq := (sq_le_sq₀
      (mul_nonneg (div_nonneg hLR.le hmR.le) (norm_nonneg _))
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ht
    nlinarith [sq_nonneg (‖qResidue m‖ - ‖compensatedResidue m L‖)]
  have halg2 : ((L : ℝ) - 8 * m) / (4 * zetaTwo * (m : ℝ) ^ 2) =
      (L / (2 * zetaTwo * (m : ℝ) ^ 2) - 2 * (2 / (zetaTwo * (m : ℝ)))) / 2 := by
    field_simp
    ring
  rw [halg2]
  linarith

end RiemannResearch.RH.QResidueAnchorScreening
