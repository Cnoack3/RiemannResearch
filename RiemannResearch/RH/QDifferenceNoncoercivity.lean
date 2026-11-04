/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDifferenceGram
import RiemannResearch.RH.QConductorEstimates
import RiemannResearch.RH.QPhysicalDifference
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
/-!
# Physical difference is not coercive on legal prime atoms

Source: elementary consequences of the exact derivative Gram in QDifferenceGram
and the complete-Q head/tail estimate in QConductorEstimates. These calculations
were independently assembled in the tensor-approximation discussion of
2026-11-04; no claim of mathematical novelty is made.

The prime-atom amplification grows at least as p / (2 * zetaTwo), so a uniform
inverse estimate cannot transfer derivative approximation to primitive
approximation. The scaled atoms sqrt(p) * g_p have derivative norm squared
2 * (p - 1) / p^2 but primitive norm squared at least 1 / (2 * zetaTwo).

These are obstruction results, not an RH proof. A bounded full-energy legal
family or the regularized budget in QPrimitiveEnergyClosure is still required.
The displayed limit of the derivative energies as p tends to infinity is an
elementary mathematical consequence; this module checks the finite identities
and inequalities.
-/

noncomputable section
open RiemannResearch.RH.ZetaTwoHilbert RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.RH.QPhysicalDifference RiemannResearch.RH.QDifferenceGram
namespace RiemannResearch.RH.QDifferenceNoncoercivity
theorem difference_residue_norm_sq (d : ℕ) (hd : 2 ≤ d) :
    ‖differenceCLM (qResidue d)‖ ^ 2 = 2 * ((d : ℝ) - 1) / (d : ℝ)^3 := by
  rw [← real_inner_self_eq_norm_sq, inner_difference_qResidue d d hd hd]
  simp only [derivativeGram, Nat.lcm_self]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  field_simp
  ring

theorem residue_inverse_amplification (d : ℕ) (hd : 2 ≤ d) :
    ((d : ℝ) / (2 * zetaTwo)) * ‖differenceCLM (qResidue d)‖ ^ 2 ≤
      ‖qResidue d‖ ^ 2 := by
  rw [difference_residue_norm_sq d hd]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  convert qResidue_norm_sq_ge_head d (by omega) using 1 <;> field_simp

theorem residue_exceeds_coercivity_constant (d : ℕ) (hd : 2 ≤ d)
    (C : ℝ) (hC : 2 * zetaTwo * C < (d : ℝ)) :
    C * ‖differenceCLM (qResidue d)‖ ^ 2 < ‖qResidue d‖ ^ 2 := by
  have hz : 0 < 2 * zetaTwo := mul_pos (by norm_num) zetaTwo_pos
  have hc : C < (d : ℝ) / (2 * zetaTwo) :=
    (lt_div_iff₀ hz).mpr (by nlinarith [hC])
  have hdR : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have he : 0 < ‖differenceCLM (qResidue d)‖ ^ 2 := by
    rw [difference_residue_norm_sq d hd]
    positivity
  exact (mul_lt_mul_of_pos_right hc he).trans_le (residue_inverse_amplification d hd)

/-- No constant controls primitive energy by derivative energy, even on prime atoms. -/
theorem exists_prime_exceeding_coercivity (C : ℝ) :
    ∃ p : ℕ, p.Prime ∧
      C * ‖differenceCLM (qResidue p)‖ ^ 2 < ‖qResidue p‖ ^ 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * zetaTwo * C)
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
  exact ⟨p, hp, residue_exceeds_coercivity_constant p hp.two_le C
    (hn.trans_le (by exact_mod_cast hnp))⟩

def scaledResidue (d : ℕ) : QHilbert := Real.sqrt (d : ℝ) • qResidue d

theorem scaledResidue_norm_sq (d : ℕ) :
    ‖scaledResidue d‖ ^ 2 = (d : ℝ) * ‖qResidue d‖ ^ 2 := by
  simp only [scaledResidue, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]

theorem scaledResidue_difference_norm_sq (d : ℕ) (hd : 2 ≤ d) :
    ‖differenceCLM (scaledResidue d)‖ ^ 2 =
      2 * ((d : ℝ) - 1) / (d : ℝ)^2 := by
  simp only [scaledResidue, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  rw [difference_residue_norm_sq d hd]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  field_simp

theorem scaledResidue_norm_sq_lower (d : ℕ) (hd : 2 ≤ d) :
    1 / (2 * zetaTwo) ≤ ‖scaledResidue d‖ ^ 2 := by
  rw [scaledResidue_norm_sq]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  calc
    _ = (d : ℝ) * (1 / (2 * zetaTwo * (d : ℝ))) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (qResidue_norm_sq_ge_half_div d hd)
      (Nat.cast_nonneg d)
end RiemannResearch.RH.QDifferenceNoncoercivity
