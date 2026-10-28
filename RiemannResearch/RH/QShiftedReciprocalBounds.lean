/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
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


/-- Exact one-parameter energy certificate for change-of-metric displacement.
Source: algebraic continuation of the user's two-residual calculation. -/
theorem displacement_energy_remainder_param (r d : QHilbert) (a : ℝ)
    (hrd : inner ℝ d r = 0)
    (hnormal : inner ℝ d (B (r + d)) = ‖d‖ ^ 2) :
    ‖r‖ ^ 2 = (a ^ 2 - 2 * a) * ‖d‖ ^ 2 +
      (a / 2) * inner ℝ (r + (2 - a) • d) (B (r + (2 - a) • d)) +
      (‖r + a • d‖ ^ 2 -
        (a / 2) * inner ℝ (r + a • d) (B (r + a • d))) := by
  have hdr : inner ℝ r d = 0 := by rw [real_inner_comm]; exact hrd
  have hsym : inner ℝ r (B d) = inner ℝ d (B r) := by
    rw [← B_symmetric, real_inner_comm]
  rw [map_add, inner_add_right] at hnormal
  have hc : inner ℝ d (B r) = ‖d‖ ^ 2 - inner ℝ d (B d) := by linarith
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, inner_smul_right, norm_add_sq_real,
    norm_smul, hdr, hsym, hc, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The shifted reciprocal has quadratic form at most half the identity. -/
theorem twice_B_inner_le_norm_sq (f : QHilbert) :
    2 * inner ℝ f (B f) ≤ ‖f‖ ^ 2 := by
  have h := (real_inner_le_norm f (B f)).trans
    (mul_le_mul_of_nonneg_left (B_norm_le_half f) (norm_nonneg f))
  nlinarith


/-- At parameter four, both displayed remainder terms are nonnegative. -/
theorem displacement_energy_remainder (r d : QHilbert)
    (hrd : inner ℝ d r = 0)
    (hnormal : inner ℝ d (B (r + d)) = ‖d‖ ^ 2) :
    ‖r‖ ^ 2 = 8 * ‖d‖ ^ 2 +
      2 * inner ℝ (r - (2 : ℝ) • d) (B (r - (2 : ℝ) • d)) +
      (‖r + (4 : ℝ) • d‖ ^ 2 -
        2 * inner ℝ (r + (4 : ℝ) • d) (B (r + (4 : ℝ) • d))) := by
  have hdr : inner ℝ r d = 0 := by rw [real_inner_comm]; exact hrd
  have hsym : inner ℝ r (B d) = inner ℝ d (B r) := by
    rw [← B_symmetric, real_inner_comm]
  rw [map_add, inner_add_right] at hnormal
  simp only [map_sub, map_add, map_smul, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right,
    norm_add_sq_real, norm_smul, hdr]
  norm_num
  nlinarith

theorem strict_displacement_energy_bound (r d : QHilbert)
    (hrd : inner ℝ d r = 0)
    (hnormal : inner ℝ d (B (r + d)) = ‖d‖ ^ 2)
    (hr : r ≠ 0) :
    8 * ‖d‖ ^ 2 < ‖r‖ ^ 2 := by
  have hne : r - (2 : ℝ) • d ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    rw [he, inner_smul_right, real_inner_self_eq_norm_sq] at hrd
    have hd : d = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg d])
    exact hr (by simpa [hd] using he)
  have hpos : 0 < inner ℝ (r - (2 : ℝ) • d) (B (r - (2 : ℝ) • d)) :=
    lt_of_le_of_ne (B_positive _) (Ne.symm (fun h => hne (B_faithful _ h)))
  have he := displacement_energy_remainder r d hrd hnormal
  have hu := twice_B_inner_le_norm_sq (r + (4 : ℝ) • d)
  linarith

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


/-- Exact residual-dependent variance decomposition, with every square retained. -/
theorem movingCorrection_variance_exact (N : ℕ) (t : ℝ) :
  ‖B (residual N)‖ ^ 2 =
    ‖movingCorrection N‖ ^ 2 +
    2 * t * inner ℝ (residual N) (B (residual N)) - t ^ 2 * error N +
    ‖B (residual N) - movingCorrection N - t • residual N‖ ^ 2 := by
  have ho : inner ℝ (residual N) (movingCorrection N) = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal
      ((stage N).starProjection_apply_mem _) (residual_mem_orthogonal N)
  have he : inner ℝ (B (residual N) - movingCorrection N) (residual N) =
      inner ℝ (residual N) (B (residual N)) := by
    rw [real_inner_comm, inner_sub_right, ho, sub_zero]
  have hp := RiemannResearch.LinearAlgebra.inner_residualized_eq_schur
    (stage N) (B (residual N)) (B (residual N))
  simp only [real_inner_self_eq_norm_sq] at hp
  change ‖B (residual N) - movingCorrection N‖ ^ 2 =
    ‖B (residual N)‖ ^ 2 - ‖movingCorrection N‖ ^ 2 at hp
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, he, hp, error]
  ring

/-- The squared residual multiplier moment is an unconditional energy subtraction. -/
theorem movingCorrection_variance_bound (N : ℕ) :
  error N * ‖movingCorrection N‖ ^ 2 +
      (inner ℝ (residual N) (B (residual N))) ^ 2 ≤
    error N * ‖B (residual N)‖ ^ 2 := by
  have ho : inner ℝ (residual N) (movingCorrection N) = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal
      ((stage N).starProjection_apply_mem _) (residual_mem_orthogonal N)
  have he : inner ℝ (residual N) (B (residual N) - movingCorrection N) =
      inner ℝ (residual N) (B (residual N)) := by
    rw [inner_sub_right, ho, sub_zero]
  have hp := RiemannResearch.LinearAlgebra.inner_residualized_eq_schur
    (stage N) (B (residual N)) (B (residual N))
  simp only [real_inner_self_eq_norm_sq] at hp
  change ‖B (residual N) - movingCorrection N‖ ^ 2 =
    ‖B (residual N)‖ ^ 2 - ‖movingCorrection N‖ ^ 2 at hp
  have hc := abs_real_inner_le_norm (residual N)
    (B (residual N) - movingCorrection N)
  have hs := mul_le_mul hc hc (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [← pow_two, sq_abs, he, ← pow_two, mul_pow, hp] at hs
  change ‖residual N‖ ^ 2 * ‖movingCorrection N‖ ^ 2 +
    (inner ℝ (residual N) (B (residual N))) ^ 2 ≤
    ‖residual N‖ ^ 2 * ‖B (residual N)‖ ^ 2
  nlinarith

end RiemannResearch.RH.QShiftedReciprocal
