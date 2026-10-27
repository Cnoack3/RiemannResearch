/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocalBounds
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Centered resolvent for the Q/P squarefree displacement

Source: user-provided two-residual measure-change agenda and the exact
projection derivation developed on 27 October 2026.

Let `d` be the Q/P projection displacement, `r` the Q residual, and
`b = Π(B r)` the projected smoothed residual. Projecting the already proved
orthogonal witness gives the exact fixed-point identity

  d = b + Π(B d).

Centering the diagonal multiplier at `1/4` gives the sharper identity

  d = (4/3) b + R d,
  R f = (4/3) Π(B f - (1/4) f),

with `‖R f‖ ≤ (1/3) ‖f‖`. The recursive finite resolvent therefore has an
exact signed one-step remainder and a geometric Hilbert-norm error.

These declarations do not prove physical boundedness. Evaluation on the Q
Hilbert space has a site-dependent norm, and no weighted-supremum stability of
the squarefree projection is assumed or proved here.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeDisplacementResolvent
open ZetaTwoHilbert ZetaTwoOptimizerStage
open QShiftedReciprocal QSquarefreeSmoothedProjection
open QSquarefreeDisplacementRigidity

/-- The displacement is the projection of the smoothed Pareto residual. -/
theorem displacement_eq_projected_pResidual :
    displacement = closure.starProjection (B pResidual) := by
  have hzero : closure.starProjection witness = 0 := by
    have h1 := Submodule.inner_right_of_mem_orthogonal
      (closure.starProjection_apply_mem witness) witness_mem_orthogonal
    have h2 := Submodule.inner_right_of_mem_orthogonal
      (closure.starProjection_apply_mem witness)
      (Submodule.sub_starProjection_mem_orthogonal (K := closure) witness)
    rw [inner_sub_right, h1, real_inner_self_eq_norm_sq] at h2
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (closure.starProjection witness)]
  have heq : closure.starProjection (B pResidual) = displacement := by
    rw [witness, map_sub,
      Submodule.starProjection_eq_self_iff.mpr displacement_mem] at hzero
    exact sub_eq_zero.mp hzero
  exact heq.symm

/-- Exact uncentered response equation `d = b + Π(B d)`. -/
theorem displacement_fixed_point :
    displacement =
      correction + closure.starProjection (B displacement) := by
  calc
    displacement = closure.starProjection (B pResidual) :=
      displacement_eq_projected_pResidual
    _ = closure.starProjection (B (limitingResidual + displacement)) := by
      rw [← pResidual_eq_residual_add_displacement]
    _ = closure.starProjection (B limitingResidual) +
        closure.starProjection (B displacement) := by rw [map_add, map_add]
    _ = correction + closure.starProjection (B displacement) := rfl

/-- Centered projected feedback. Its factor `4/3` normalizes the fixed-point
equation after moving the scalar quarter of the displacement to the left. -/
def centeredFeedback (f : QHilbert) : QHilbert :=
  (4 / 3 : ℝ) • closure.starProjection (B f - (1 / 4 : ℝ) • f)

theorem centeredFeedback_sub (f g : QHilbert) :
    centeredFeedback (f - g) = centeredFeedback f - centeredFeedback g := by
  unfold centeredFeedback
  have hinside : B (f - g) - (1 / 4 : ℝ) • (f - g) =
      (B f - (1 / 4 : ℝ) • f) - (B g - (1 / 4 : ℝ) • g) := by
    rw [map_sub, smul_sub]
    abel
  rw [hinside, map_sub, smul_sub]

/-- The centered feedback contracts Q-Hilbert norm by the explicit factor
`1/3`. -/
theorem centeredFeedback_norm_le (f : QHilbert) :
    ‖centeredFeedback f‖ ≤ (1 / 3 : ℝ) * ‖f‖ := by
  have hp : ‖closure.starProjection (B f) -
        (1 / 4 : ℝ) • closure.starProjection f‖ ≤
      ‖B f - (1 / 4 : ℝ) • f‖ := by
    calc
      _ = ‖closure.starProjection (B f - (1 / 4 : ℝ) • f)‖ := by
        rw [map_sub, map_smul]
      _ ≤ ‖closure.starProjection‖ * ‖B f - (1 / 4 : ℝ) • f‖ :=
        closure.starProjection.le_opNorm _
      _ ≤ _ := by
        simpa using mul_le_mul_of_nonneg_right
          (Submodule.starProjection_norm_le closure) (norm_nonneg _)
  unfold centeredFeedback
  rw [map_sub, map_smul, norm_smul, Real.norm_eq_abs]
  norm_num
  calc
    (4 / 3 : ℝ) *
        ‖closure.starProjection (B f) - (1 / 4 : ℝ) • closure.starProjection f‖
        ≤ (4 / 3 : ℝ) * ‖B f - (1 / 4 : ℝ) • f‖ :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ (4 / 3 : ℝ) * ((1 / 4 : ℝ) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (B_centered_norm_le f) (by norm_num)
    _ = (1 / 3 : ℝ) * ‖f‖ := by ring

/-- Exact centered response equation `d = (4/3)b + R d`. -/
theorem displacement_centered_fixed_point :
    displacement = (4 / 3 : ℝ) • correction + centeredFeedback displacement := by
  let c := closure.starProjection
    (B displacement - (1 / 4 : ℝ) • displacement)
  have hP : closure.starProjection (B displacement) =
      (1 / 4 : ℝ) • displacement + c := by
    dsimp only [c]
    rw [map_sub, map_smul,
      Submodule.starProjection_eq_self_iff.mpr displacement_mem]
    module
  have hbase : displacement =
      (correction + c) + (1 / 4 : ℝ) • displacement := by
    calc
      displacement =
          correction + closure.starProjection (B displacement) :=
        displacement_fixed_point
      _ = correction + ((1 / 4 : ℝ) • displacement + c) := by rw [hP]
      _ = _ := by abel
  have hx : (3 / 4 : ℝ) • displacement = correction + c := by
    calc
      (3 / 4 : ℝ) • displacement =
          displacement - (1 / 4 : ℝ) • displacement := by module
      _ = correction + c := sub_eq_iff_eq_add.mpr hbase
  calc
    displacement = (4 / 3 : ℝ) • ((3 / 4 : ℝ) • displacement) := by module
    _ = (4 / 3 : ℝ) • (correction + c) := by rw [hx]
    _ = (4 / 3 : ℝ) • correction + (4 / 3 : ℝ) • c := by rw [smul_add]
    _ = (4 / 3 : ℝ) • correction + centeredFeedback displacement := by
      rfl

/-- The finite centered Neumann resolvent, defined without an infinite-series
interchange. -/
def resolventApprox : ℕ → QHilbert
  | 0 => 0
  | n + 1 => (4 / 3 : ℝ) • correction + centeredFeedback (resolventApprox n)

/-- Exact signed remainder recursion for the finite resolvent. -/
theorem resolvent_error_succ (n : ℕ) :
    displacement - resolventApprox (n + 1) =
      centeredFeedback (displacement - resolventApprox n) := by
  calc
    displacement - resolventApprox (n + 1) =
        ((4 / 3 : ℝ) • correction + centeredFeedback displacement) -
          resolventApprox (n + 1) :=
      congrArg (fun x => x - resolventApprox (n + 1))
        displacement_centered_fixed_point
    _ = ((4 / 3 : ℝ) • correction + centeredFeedback displacement) -
        ((4 / 3 : ℝ) • correction + centeredFeedback (resolventApprox n)) := by
      rw [resolventApprox]
    _ = centeredFeedback displacement - centeredFeedback (resolventApprox n) := by
      abel
    _ = centeredFeedback (displacement - resolventApprox n) := by
      rw [centeredFeedback_sub]

/-- Quantitative finite-resolvent error. No limit interchange is used: the
bound follows by induction from the exact signed remainder recursion. -/
theorem resolvent_error_norm_le (n : ℕ) :
    ‖displacement - resolventApprox n‖ ≤
      (1 / 3 : ℝ) ^ n * ‖displacement‖ := by
  induction n with
  | zero =>
      simp [resolventApprox]
  | succ n ih =>
      rw [resolvent_error_succ]
      calc
        ‖centeredFeedback (displacement - resolventApprox n)‖ ≤
            (1 / 3 : ℝ) * ‖displacement - resolventApprox n‖ :=
          centeredFeedback_norm_le _
        _ ≤ (1 / 3 : ℝ) *
            ((1 / 3 : ℝ) ^ n * ‖displacement‖) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 3 : ℝ) ^ (n + 1) * ‖displacement‖ := by
          rw [pow_succ]
          ring

/-- A coarse uncentered consequence useful for comparison with the correction
energy: `‖d‖ ≤ 2 ‖b‖`. -/
theorem displacement_norm_le_correction :
    ‖displacement‖ ≤ 2 * ‖correction‖ := by
  have hp : ‖closure.starProjection (B displacement)‖ ≤
      (1 / 2 : ℝ) * ‖displacement‖ := by
    calc
      _ ≤ ‖closure.starProjection‖ * ‖B displacement‖ :=
        closure.starProjection.le_opNorm _
      _ ≤ ‖B displacement‖ := by
        simpa using mul_le_mul_of_nonneg_right
          (Submodule.starProjection_norm_le closure) (norm_nonneg _)
      _ ≤ _ := B_norm_le_half displacement
  have ht := norm_add_le correction (closure.starProjection (B displacement))
  have heq := displacement_fixed_point
  rw [← heq] at ht
  nlinarith [norm_nonneg displacement, norm_nonneg correction]

end RiemannResearch.RH.QSquarefreeDisplacementResolvent
