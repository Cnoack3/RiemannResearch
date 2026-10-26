/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeBoundary
import RiemannResearch.RH.QSquarefreeKernelScreening
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QDivisibilityDensity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# An arithmetic spectral gap for the shifted reciprocal

Source: the user-provided moving-head research handoff, 26 October 2026,
and the existing squarefree four-site identity. The new argument combines
that identity with an exact positive quadratic remainder. It applies to
the entire kernel of the four-site functional, including every squarefree
legal vector, the target, and every actual projection residual.

The resulting 59/120 compression bound and 1/60 coercivity at parameter 2
use no RH or open arithmetic hypothesis. They do not give a uniform physical
moving-head bound or prove residual vanishing.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeReciprocalGap
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QShiftedReciprocal QSquarefreeBoundary QSquarefreeKernelScreening

private theorem qSequence_succ_coordinates (f : QHilbert) (n : ℕ) :
    qSequence f (n + 1) = ((n + 1 : ℕ) : ℝ) * Real.sqrt zetaTwo * f n := by
  rw [qSequence_succ]
  apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n)))).mpr
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  calc
    f n = f n * (((n + 1 : ℕ) : ℝ) *
        (Real.sqrt (qWeight n) * Real.sqrt zetaTwo)) := by
      rw [QDivisibilityDensity.sqrt_qWeight_mul_sqrt_zetaTwo]
      field_simp [hn]
    _ = _ := by ring

theorem fourSite_zero_coordinates {f : QHilbert} (hf : fourSiteFunctional f = 0) :
    f 0 = 2 * f 1 + 3 * f 2 - 4 * f 3 := by
  rw [fourSiteFunctional_apply] at hf
  have h1 := qSequence_succ_coordinates f 0
  have h2 := qSequence_succ_coordinates f 1
  have h3 := qSequence_succ_coordinates f 2
  have h4 := qSequence_succ_coordinates f 3
  norm_num only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_add, one_mul] at h1 h2 h3 h4
  rw [h1, h2, h3, h4] at hf
  have hz : Real.sqrt zetaTwo ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr zetaTwo_pos)
  have he : Real.sqrt zetaTwo * (f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3) = 0 := by
    nlinarith [hf]
  have he' := (mul_eq_zero.mp he).resolve_left hz
  linarith

/-- The finite arithmetic step is an exact sum of three nonnegative squares. -/
theorem fourSite_quadratic_exact (x y z : ℝ) :
    19 * x ^ 2 + 29 * y ^ 2 + 35 * z ^ 2 - (2*x + 3*y - 4*z)^2 =
      (15*x - 6*y + 8*z)^2 / 15 +
      2 * (22*y + 19*z)^2 / 55 + 53 * z^2 / 33 := by
  ring

def headRemainder (f : QHilbert) : ℝ :=
  (15*f 1 - 6*f 2 + 8*f 3)^2 / 15 +
    2 * (22*f 2 + 19*f 3)^2 / 55 + 53 * (f 3)^2 / 33

def spectralDefect (f : QHilbert) (n : ℕ) : ℝ :=
  ((59 : ℝ)/120 - 1/((n : ℝ)+2)) * (f n)^2

theorem headRemainder_nonneg (f : QHilbert) : 0 ≤ headRemainder f := by
  unfold headRemainder
  positivity

private theorem reciprocal_square_summable (f : QHilbert) :
    Summable (fun n : ℕ => (f n)^2 / ((n : ℝ)+2)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _
    (qCoordinate_square_summable f)
  intro n
  exact div_le_self (sq_nonneg _) (by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith)

theorem spectralDefect_summable (f : QHilbert) : Summable (spectralDefect f) := by
  apply (((qCoordinate_square_summable f).mul_left ((59 : ℝ)/120)).sub
    (reciprocal_square_summable f)).congr
  intro n
  unfold spectralDefect
  ring

theorem spectralDefect_tsum (f : QHilbert) :
    (∑' n : ℕ, spectralDefect f n) =
      ((59 : ℝ)/120) * ‖f‖^2 - inner ℝ f (B f) := by
  have he : spectralDefect f = fun n : ℕ =>
      ((59 : ℝ)/120) * (f n)^2 - (f n)^2 / ((n : ℝ)+2) := by
    funext n
    unfold spectralDefect
    ring
  rw [he, Summable.tsum_sub
    ((qCoordinate_square_summable f).mul_left ((59 : ℝ)/120))
    (reciprocal_square_summable f), tsum_mul_left, ← qNorm_sq, ← B_inner_tsum]

/-- Exact spectral deficit, including the entire nonnegative infinite tail. -/
theorem reciprocal_gap_exact {f : QHilbert} (hf : fourSiteFunctional f = 0) :
    ((59 : ℝ)/120) * ‖f‖^2 - inner ℝ f (B f) =
      headRemainder f / 120 + ∑' n : ℕ, spectralDefect f (n + 4) := by
  rw [← spectralDefect_tsum,
    ← (spectralDefect_summable f).sum_add_tsum_nat_add 4]
  congr 1
  have hcoord := fourSite_zero_coordinates hf
  norm_num [Finset.sum_range_succ, spectralDefect]
  rw [hcoord]
  unfold headRemainder
  ring

theorem spectralDefect_tail_nonneg (f : QHilbert) (n : ℕ) :
    0 ≤ spectralDefect f (n + 4) := by
  unfold spectralDefect
  apply mul_nonneg _ (sq_nonneg _)
  apply sub_nonneg.mpr
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n + 4 : ℕ) + 2)).mpr
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- Arithmetic improves the ambient multiplier upper bound 1/2 to 59/120. -/
theorem B_inner_le_of_fourSite_zero {f : QHilbert} (hf : fourSiteFunctional f = 0) :
    inner ℝ f (B f) ≤ ((59 : ℝ)/120) * ‖f‖^2 := by
  have he := reciprocal_gap_exact hf
  have hh := headRemainder_nonneg f
  have ht : 0 ≤ ∑' n : ℕ, spectralDefect f (n + 4) :=
    tsum_nonneg (spectralDefect_tail_nonneg f)
  linarith

/-- Although the ambient metric at t=2 vanishes at physical site 1,
it stays coercive on the four-site kernel, hence on the legal affine space. -/
theorem parameter_two_coercive {f : QHilbert} (hf : fourSiteFunctional f = 0) :
    (1 : ℝ)/60 * ‖f‖^2 ≤ inner ℝ f (f - (2 : ℝ) • B f) := by
  rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  nlinarith [B_inner_le_of_fourSite_zero hf]

theorem closure_B_inner_le {f : QHilbert} (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    inner ℝ f (B f) ≤ ((59 : ℝ)/120) * ‖f‖^2 :=
  B_inner_le_of_fourSite_zero (fourSiteFunctional_zero_on_closure hf)

theorem fourSite_zero_residual (N : ℕ) : fourSiteFunctional (residual N) = 0 := by
  rw [← inner_fourSiteVector]
  exact residual_inner_fourSiteVector N

theorem residual_B_inner_le (N : ℕ) :
    inner ℝ (residual N) (B (residual N)) ≤ ((59 : ℝ)/120) * error N :=
  B_inner_le_of_fourSite_zero (fourSite_zero_residual N)

theorem residual_parameter_two_coercive (N : ℕ) :
    (1 : ℝ)/60 * error N ≤
      inner ℝ (residual N) (residual N - (2 : ℝ) • B (residual N)) :=
  parameter_two_coercive (fourSite_zero_residual N)

theorem affine_parameter_two_coercive {f : QHilbert}
    (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    (1 : ℝ)/60 * ‖qOne - f‖^2 ≤
      inner ℝ (qOne - f) (qOne - f - (2 : ℝ) • B (qOne - f)) := by
  apply parameter_two_coercive
  rw [map_sub, fourSiteFunctional_qOne, fourSiteFunctional_zero_on_closure hf, sub_self]

/-- An unconditional squarefree improvement of the universal quarter bound.
The signed two-vector energy difference supplies the estimate. -/
theorem movingCorrection_norm_le_squarefree (N : ℕ) :
    ‖QSquarefreeSmoothedProjection.movingCorrection N‖ ≤
      ((59 : ℝ)/240) * ‖residual N‖ := by
  let r : QHilbert := residual N
  let b : QHilbert := QSquarefreeSmoothedProjection.movingCorrection N
  let t : ℝ := 240 / 59
  have hbmem : b ∈ stage N := (stage N).starProjection_apply_mem _
  have hrb : inner ℝ r b = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hbmem (residual_mem_orthogonal N)
  have hbr : inner ℝ b (B r) = ‖b‖^2 := by
    have h := Submodule.inner_right_of_mem_orthogonal hbmem
      (Submodule.sub_starProjection_mem_orthogonal (K := stage N) (B r))
    change inner ℝ b (B r - b) = 0 at h
    rw [inner_sub_right, real_inner_self_eq_norm_sq] at h
    linarith
  have hrBb : inner ℝ r (B b) = ‖b‖^2 := by
    rw [← B_symmetric, real_inner_comm]
    exact hbr
  have hplus : fourSiteFunctional (r + t • b) = 0 := by
    rw [map_add, map_smul, fourSite_zero_residual N,
      fourSiteFunctional_stage hbmem, smul_zero, add_zero]
  have hexact : inner ℝ (r + t • b) (B (r + t • b)) -
      inner ℝ (r - t • b) (B (r - t • b)) = 4*t*‖b‖^2 := by
    simp only [map_add, map_sub, map_smul, inner_add_left, inner_sub_left,
      inner_add_right, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hbr, hrBb]
    ring
  have hnorm : ‖r + t • b‖^2 = ‖r‖^2 + t^2 * ‖b‖^2 := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right, hrb]
    ring
  have hu := B_inner_le_of_fourSite_zero hplus
  have hl := B_positive (r - t • b)
  rw [hnorm] at hu
  have hs : ‖b‖^2 ≤ ((59 : ℝ)/240)^2 * ‖r‖^2 := by
    dsimp [t] at hexact hu
    nlinarith
  change ‖b‖ ≤ ((59 : ℝ)/240) * ‖r‖
  nlinarith [norm_nonneg b, norm_nonneg r]

end RiemannResearch.RH.QSquarefreeReciprocalGap
