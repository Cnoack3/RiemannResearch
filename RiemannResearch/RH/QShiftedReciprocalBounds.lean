/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Centered reciprocal multiplier bounds

Source: user-provided squarefree projection regularity agenda; elementary
spectral centering of the diagonal multiplier. These are Hilbert norm bounds,
not physical uniform bounds on growing heads.
-/

noncomputable section
namespace RiemannResearch.RH.QShiftedReciprocal
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeSmoothedProjection

theorem B_centered_norm_le (f : QHilbert) :
    ‖B f - (1 / 4 : ℝ) • f‖ ≤ (1 / 4 : ℝ) * ‖f‖ := by
  have hsq : ‖B f - (1 / 4 : ℝ) • f‖ ^ 2 ≤ ‖(1 / 4 : ℝ) • f‖ ^ 2 := by
    rw [qNorm_sq, qNorm_sq]
    apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _)
      (qCoordinate_square_summable _)
    intro n
    change (f n / ((n : ℝ) + 2) - (1 / 4 : ℝ) * f n) ^ 2 ≤
      ((1 / 4 : ℝ) * f n) ^ 2
    have hd : 0 < (n : ℝ) + 2 := by positivity
    have hlo : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
    have hhi : 1 / ((n : ℝ) + 2) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hd).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hc : (1 / ((n : ℝ) + 2) - (1 / 4 : ℝ)) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (f n))
    convert hm using 1 <;> ring
  rw [norm_smul, Real.norm_eq_abs] at hsq
  norm_num at hsq
  nlinarith [norm_nonneg (B f - (1 / 4 : ℝ) • f), norm_nonneg f]

theorem B_norm_le_half (f : QHilbert) : ‖B f‖ ≤ (1 / 2 : ℝ) * ‖f‖ := by
  have h := norm_add_le (B f - (1 / 4 : ℝ) • f) ((1 / 4 : ℝ) • f)
  rw [sub_add_cancel, norm_smul, Real.norm_eq_abs] at h
  norm_num at h
  linarith [B_centered_norm_le f]

theorem projected_B_norm_le_quarter (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] {r : QHilbert} (hr : r ∈ Sᗮ) :
    ‖S.starProjection (B r)‖ ≤ (1 / 4 : ℝ) * ‖r‖ := by
  have hz : S.starProjection r = 0 := by
    have h1 := Submodule.inner_right_of_mem_orthogonal (S.starProjection_apply_mem r) hr
    have h2 := Submodule.inner_right_of_mem_orthogonal (S.starProjection_apply_mem r)
      (Submodule.sub_starProjection_mem_orthogonal (K := S) r)
    rw [inner_sub_right, h1, real_inner_self_eq_norm_sq] at h2
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (S.starProjection r)]
  have he : S.starProjection (B r - (1 / 4 : ℝ) • r) = S.starProjection (B r) := by
    simp only [map_sub, map_smul, hz, smul_zero, sub_zero]
  rw [← he]
  calc
    _ ≤ ‖S.starProjection‖ * ‖B r - (1 / 4 : ℝ) • r‖ := S.starProjection.le_opNorm _
    _ ≤ ‖B r - (1 / 4 : ℝ) • r‖ := by
      simpa using mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le S) (norm_nonneg _)
    _ ≤ (1 / 4 : ℝ) * ‖r‖ := B_centered_norm_le r

theorem movingCorrection_norm_le_quarter (N : ℕ) :
    ‖movingCorrection N‖ ≤ (1 / 4 : ℝ) * ‖residual N‖ :=
  projected_B_norm_le_quarter (stage N) (residual_mem_orthogonal N)


/-- The sharp universal metric-displacement estimate for the Q/P weight ratio.
It controls Hilbert energy, not the physical supremum norm. -/
theorem sharp_displacement_energy_bound (r d : QHilbert)
    (hrd : inner ℝ d r = 0)
    (hnormal : inner ℝ d (B (r + d)) = ‖d‖ ^ 2) :
    8 * ‖d‖ ^ 2 ≤ ‖r‖ ^ 2 := by
  have hcenter : inner ℝ d (B (r + d) - (1 / 4 : ℝ) • (r + d)) =
      (3 / 4 : ℝ) * ‖d‖ ^ 2 := by
    rw [inner_sub_right, inner_smul_right, inner_add_right,
      hnormal, hrd, zero_add, real_inner_self_eq_norm_sq]
    ring
  have hb : (3 / 4 : ℝ) * ‖d‖ ^ 2 ≤
      ‖d‖ * ((1 / 4 : ℝ) * ‖r + d‖) := by
    rw [← hcenter]
    exact (real_inner_le_norm d _).trans
      (mul_le_mul_of_nonneg_left (B_centered_norm_le (r + d)) (norm_nonneg d))
  by_cases hd : ‖d‖ = 0
  · simp only [hd, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact sq_nonneg _
  have hdp : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg d) (Ne.symm hd)
  have hprod : ‖d‖ * (3 * ‖d‖) ≤ ‖d‖ * ‖r + d‖ := by nlinarith [hb]
  have h3 : 3 * ‖d‖ ≤ ‖r + d‖ := by nlinarith [hprod]
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ 3 * ‖d‖) h3
  have hsum : ‖r + d‖ ^ 2 = ‖r‖ ^ 2 + ‖d‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_comm, hrd]
    ring
  nlinarith [hs]


end RiemannResearch.RH.QShiftedReciprocal
