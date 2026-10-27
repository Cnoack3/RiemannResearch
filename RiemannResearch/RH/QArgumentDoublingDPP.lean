/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorProjectionParity
import RiemannResearch.RH.QArgumentDoubling
import RiemannResearch.RH.QDivisorProjectionDPP
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Physical doubling cannot preserve the divisor-mode DPP Gram kernel

Source: independently derived from the user's doubling/DPP request,
27 October 2026. The DPP terminology is supported by Russell Lyons,
"Determinantal probability measures" (2003),
https://arxiv.org/abs/math/0204325. The calculation below is independent.

The hypotheses on T are satisfied by physical argument doubling:
T(1)=1 and T(g₂)=0. The transformed mode family is not orthonormal.
Its projected parity diagonal is at least 9/4, so treating that Gram matrix
as a positive-contraction DPP kernel is impossible. This does not rule out
invariance of the particular projection residual under physical doubling.
-/

noncomputable section
namespace RiemannResearch.RH.QDivisorProjectionDPP
open ZetaTwoHilbert QDivisorHilbert

variable (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
variable (T : QHilbert →ₗ[ℝ] QHilbert)

/-- The normalized parity mode collapses to √3 times the constant under any
linear operator with the two elementary physical-doubling identities. -/
theorem doubling_normalized_two
    (hOne : T qOne = qOne) (hTwo : T (qResidue 2) = 0) :
    T (normalizedDivisorWavelet 2) = Real.sqrt 3 • qOne := by
  have hs : (Real.sqrt 3)⁻¹ * 3 = Real.sqrt 3 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hn : Real.sqrt (3 : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp [hn]
    nlinarith
  rw [normalized_two, map_smul, map_sub, map_smul, map_smul,
    hOne, hTwo, smul_zero, sub_zero, smul_smul, hs]

/-- The exact parity diagonal of the physically doubled projected Gram family. -/
theorem doubled_parity_projection_norm_sq
    (hOne : T qOne = qOne) (hTwo : T (qResidue 2) = 0) :
    ‖S.starProjection (T (normalizedDivisorWavelet 2))‖ ^ 2 =
      3 * modeKernel S 1 1 := by
  rw [doubling_normalized_two T hOne hTwo, map_smul, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [← constant_occupation S, modeLaw_occupation]

/-- The transformed parity diagonal differs from the original legal DPP
diagonal by exactly 2, independently of the optimizer error. -/
theorem doubled_parity_gram_gap
    (h2 : qResidue 2 ∈ S)
    (hOne : T qOne = qOne) (hTwo : T (qResidue 2) = 0) :
    ‖S.starProjection (T (normalizedDivisorWavelet 2))‖ ^ 2 =
      modeKernel S 2 2 + 2 := by
  rw [doubled_parity_projection_norm_sq S T hOne hTwo, parity_diagonal S h2]
  ring

/-- Legal spaces force the physically doubled Gram diagonal strictly above
the diagonal bound of any positive-contraction DPP kernel. -/
theorem doubled_parity_projection_lower
    (h2 : qResidue 2 ∈ S)
    (hOne : T qOne = qOne) (hTwo : T (qResidue 2) = 0) :
    (9 / 4 : ℝ) ≤ ‖S.starProjection (T (normalizedDivisorWavelet 2))‖ ^ 2 := by
  have hp := constant_occupation_lower S h2
  rw [modeLaw_occupation] at hp
  rw [doubled_parity_projection_norm_sq S T hOne hTwo]
  linarith

theorem doubled_parity_projection_gt_one
    (h2 : qResidue 2 ∈ S)
    (hOne : T qOne = qOne) (hTwo : T (qResidue 2) = 0) :
    1 < ‖S.starProjection (T (normalizedDivisorWavelet 2))‖ ^ 2 := by
  have h := doubled_parity_projection_lower S T h2 hOne hTwo
  linarith

/-- In particular, unnormalized physical doubling never leaves this DPP
Gram kernel invariant, even when the constant residual already vanishes. -/
theorem doubled_parity_gram_ne
    (h2 : qResidue 2 ∈ S)
    (hOne : T qOne = qOne) (hTwo : T (qResidue 2) = 0) :
    ‖S.starProjection (T (normalizedDivisorWavelet 2))‖ ^ 2 ≠
      modeKernel S 2 2 := by
  have h := doubled_parity_gram_gap S T h2 hOne hTwo
  linarith

/-- Actual physical argument doubling, instantiated from its Q-Hilbert operator. -/
theorem argument_doubling_normalized_two :
    QArgumentDoubling.doubling (normalizedDivisorWavelet 2) =
      Real.sqrt 3 • qOne :=
  doubling_normalized_two QArgumentDoubling.doubling.toLinearMap
    QArgumentDoubling.doubling_qOne QArgumentDoubling.doubling_qResidue_two

theorem argument_doubling_parity_projection_norm_sq :
    ‖S.starProjection (QArgumentDoubling.doubling (normalizedDivisorWavelet 2))‖ ^ 2 =
      3 * modeKernel S 1 1 :=
  doubled_parity_projection_norm_sq S QArgumentDoubling.doubling.toLinearMap
    QArgumentDoubling.doubling_qOne QArgumentDoubling.doubling_qResidue_two

theorem argument_doubling_parity_gram_gap (h2 : qResidue 2 ∈ S) :
    ‖S.starProjection (QArgumentDoubling.doubling (normalizedDivisorWavelet 2))‖ ^ 2 =
      modeKernel S 2 2 + 2 :=
  doubled_parity_gram_gap S QArgumentDoubling.doubling.toLinearMap h2
    QArgumentDoubling.doubling_qOne QArgumentDoubling.doubling_qResidue_two

theorem argument_doubling_parity_projection_lower (h2 : qResidue 2 ∈ S) :
    (9 / 4 : ℝ) ≤
      ‖S.starProjection (QArgumentDoubling.doubling (normalizedDivisorWavelet 2))‖ ^ 2 :=
  doubled_parity_projection_lower S QArgumentDoubling.doubling.toLinearMap h2
    QArgumentDoubling.doubling_qOne QArgumentDoubling.doubling_qResidue_two

theorem argument_doubling_parity_projection_gt_one (h2 : qResidue 2 ∈ S) :
    1 < ‖S.starProjection (QArgumentDoubling.doubling (normalizedDivisorWavelet 2))‖ ^ 2 :=
  doubled_parity_projection_gt_one S QArgumentDoubling.doubling.toLinearMap h2
    QArgumentDoubling.doubling_qOne QArgumentDoubling.doubling_qResidue_two

theorem argument_doubling_parity_gram_ne (h2 : qResidue 2 ∈ S) :
    ‖S.starProjection (QArgumentDoubling.doubling (normalizedDivisorWavelet 2))‖ ^ 2 ≠
      modeKernel S 2 2 :=
  doubled_parity_gram_ne S QArgumentDoubling.doubling.toLinearMap h2
    QArgumentDoubling.doubling_qOne QArgumentDoubling.doubling_qResidue_two

end RiemannResearch.RH.QDivisorProjectionDPP
