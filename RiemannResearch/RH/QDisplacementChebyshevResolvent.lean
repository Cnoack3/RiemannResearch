/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeDisplacementResolvent
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Two-step Chebyshev acceleration of the displacement resolvent

Golub and Varga, *Chebyshev semi-iterative methods*, I (1961), §2,
supply the normalized residual polynomial construction. For the centered
feedback on the squarefree closure its degree-two polynomial is
`(18 t² - 1)/17`. We prove its action and norm bound directly, retaining the
signed error and the exact norm-square remainder.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeDisplacementResolvent
open ZetaTwoHilbert ZetaTwoOptimizerStage
open QShiftedReciprocal QSquarefreeSmoothedProjection QSquarefreeDisplacementRigidity

private theorem centeredFeedback_mem (x : QHilbert) : centeredFeedback x ∈ closure :=
  closure.smul_mem _ (closure.starProjection_apply_mem _)

private theorem inner_projected_right (x y : QHilbert) (hx : x ∈ closure) :
    inner ℝ x (closure.starProjection y) = inner ℝ x y := by
  have h := Submodule.inner_right_of_mem_orthogonal hx
    (Submodule.sub_starProjection_mem_orthogonal (K := closure) y)
  rw [inner_sub_right] at h
  linarith

/-- The compression of the centered real multiplier is symmetric on the legal closure. -/
theorem centeredFeedback_symmetric_on (x y : QHilbert) (hx : x ∈ closure) (hy : y ∈ closure) :
    inner ℝ (centeredFeedback x) y = inner ℝ x (centeredFeedback y) := by
  unfold centeredFeedback
  rw [real_inner_smul_left, real_inner_smul_right]
  congr 1
  calc
    _ = inner ℝ y (closure.starProjection (B x - (1 / 4 : ℝ) • x)) := real_inner_comm _ _
    _ = inner ℝ y (B x - (1 / 4 : ℝ) • x) := inner_projected_right _ _ hy
    _ = inner ℝ (B x - (1 / 4 : ℝ) • x) y := real_inner_comm _ _
    _ = inner ℝ x (B y - (1 / 4 : ℝ) • y) := by
      rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, B_symmetric]
    _ = _ := (inner_projected_right _ _ hx).symm

/-- One ordinary affine centered step. -/
def centeredStep (x : QHilbert) : QHilbert :=
  (4 / 3 : ℝ) • correction + centeredFeedback x

private theorem centeredStep_error (x : QHilbert) :
    displacement - centeredStep x = centeredFeedback (displacement - x) := by
  unfold centeredStep
  rw [centeredFeedback_sub]
  calc
    _ = ((4/3:ℝ) • correction + centeredFeedback displacement) -
        ((4/3:ℝ) • correction + centeredFeedback x) :=
      congrArg (fun t => t - ((4/3:ℝ) • correction + centeredFeedback x))
        displacement_centered_fixed_point
    _ = _ := by abel

/-- A restarted quadratic Chebyshev cycle costs two centered steps. -/
def chebyshevCycle (x : QHilbert) : QHilbert :=
  (18 / 17 : ℝ) • centeredStep (centeredStep x) - (1 / 17 : ℝ) • x

theorem chebyshevCycle_error (x : QHilbert) :
    displacement - chebyshevCycle x =
      (1 / 17 : ℝ) • ((18 : ℝ) • centeredFeedback (centeredFeedback (displacement - x)) -
        (displacement - x)) := by
  rw [← centeredStep_error x, ← centeredStep_error (centeredStep x)]
  unfold chebyshevCycle
  module

/-- Exact loss of squared norm for the numerator of the residual polynomial. -/
theorem chebyshev_numerator_sq (e : QHilbert) (he : e ∈ closure) :
    ‖(18 : ℝ) • centeredFeedback (centeredFeedback e) - e‖ ^ 2 =
      ‖e‖ ^ 2 - 36 * (‖centeredFeedback e‖ ^ 2 -
        9 * ‖centeredFeedback (centeredFeedback e)‖ ^ 2) := by
  have h := centeredFeedback_symmetric_on (centeredFeedback e) e (centeredFeedback_mem e) he
  rw [real_inner_self_eq_norm_sq] at h
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, real_inner_smul_left, h]
  norm_num
  ring

theorem chebyshevCycle_error_norm (x : QHilbert) (hx : x ∈ closure) :
    ‖displacement - chebyshevCycle x‖ ≤ (1 / 17 : ℝ) * ‖displacement - x‖ := by
  let e := displacement - x
  have he : e ∈ closure := closure.sub_mem displacement_mem hx
  have hb := centeredFeedback_norm_le (centeredFeedback e)
  have hs := mul_self_le_mul_self (norm_nonneg _) hb
  have hsq := chebyshev_numerator_sq e he
  have hle : ‖(18 : ℝ) • centeredFeedback (centeredFeedback e) - e‖ ≤ ‖e‖ := by
    nlinarith [norm_nonneg e]
  rw [chebyshevCycle_error, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
  exact mul_le_mul_of_nonneg_left hle (by norm_num)

def chebyshevApprox : ℕ → QHilbert
  | 0 => 0
  | k + 1 => chebyshevCycle (chebyshevApprox k)

private theorem centeredStep_mem (x : QHilbert) : centeredStep x ∈ closure :=
  closure.add_mem (closure.smul_mem _ (closure.starProjection_apply_mem _)) (centeredFeedback_mem x)

theorem chebyshevApprox_mem (k : ℕ) : chebyshevApprox k ∈ closure := by
  induction k with
  | zero => exact closure.zero_mem
  | succ k ih =>
    exact closure.sub_mem (closure.smul_mem _ (centeredStep_mem _)) (closure.smul_mem _ ih)

/-- After 2k feedback evaluations the restarted error factor is 17⁻ᵏ. -/
theorem chebyshevApprox_error_norm (k : ℕ) :
    ‖displacement - chebyshevApprox k‖ ≤ (1 / 17 : ℝ)^k * ‖displacement‖ := by
  induction k with
  | zero => simp [chebyshevApprox]
  | succ k ih =>
    calc
      _ ≤ (1 / 17 : ℝ) * ‖displacement - chebyshevApprox k‖ :=
        chebyshevCycle_error_norm _ (chebyshevApprox_mem k)
      _ ≤ _ := (mul_le_mul_of_nonneg_left ih (by norm_num : 0 ≤ (1/17:ℝ))).trans_eq (by ring)

end RiemannResearch.RH.QSquarefreeDisplacementResolvent
