/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.TikhonovQuadratic
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QReciprocalFiniteHead
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Finite dual certificates for reciprocal regularization

Source: user-provided Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf,
Sections 8.3--8.4, continued on 8 November 2026. The exact dual pairing
retains both the reciprocal error and the actual residual tail.
No upper estimate for the regularized minimum is assumed or established.
-/

noncomputable section
open scoped Topology BigOperators

namespace RiemannResearch.RH.QReciprocalDualCertificate
open ZetaTwoHilbert QFullResidueProjection QFullDisplacement
open QFiniteSupportDualCriterion QShiftedReciprocal QReciprocalFiniteHead

/-- The finite dual identity uses any target and any orthogonal detector. -/
theorem reciprocal_head_dual_identity_of_orthogonal (N : ℕ)
    (x r v : QHilbert) (hvr : inner ℝ v r = 0) :
    inner ℝ x (finiteHead N r) =
      inner ℝ (B (x - v)) (inverseFiniteHead N r) -
        inner ℝ v (r - finiteHead N r) := by
  rw [B_symmetric, B_inverseFiniteHead, inner_sub_left, inner_sub_right, hvr]
  ring

/-- Every orthogonal detector provides a reciprocal-error/norm tradeoff. -/
theorem reciprocal_head_dual_bound_of_orthogonal (N : ℕ)
    (x r v : QHilbert) (hvr : inner ℝ v r = 0) :
    |inner ℝ x (finiteHead N r)| ≤
      ‖B (x - v)‖ * ‖inverseFiniteHead N r‖ +
        ‖v‖ * ‖r - finiteHead N r‖ := by
  rw [reciprocal_head_dual_identity_of_orthogonal N x r v hvr]
  exact (abs_sub _ _).trans (add_le_add (abs_real_inner_le_norm _ _)
    (abs_real_inner_le_norm _ _))

/-- Exact dual identity; all tails and the complete reciprocal error remain. -/
theorem reciprocal_head_dual_identity (N : ℕ) (v : QHilbert)
    (hv : v ∈ closure) :
    inner ℝ qOne (finiteHead N qResidual) =
      inner ℝ (B (qOne - v)) (inverseFiniteHead N qResidual) -
        inner ℝ v (qResidual - finiteHead N qResidual) :=
  reciprocal_head_dual_identity_of_orthogonal N qOne qResidual v
    (Submodule.inner_right_of_mem_orthogonal hv qResidual_mem_orthogonal)

/-- Each finite inverse head is a rigorous cost-profile dual certificate. -/
theorem reciprocal_head_dual_bound (N : ℕ) (v : QHilbert)
    (hv : v ∈ closure) :
    |inner ℝ qOne (finiteHead N qResidual)| ≤
      ‖B (qOne - v)‖ * ‖inverseFiniteHead N qResidual‖ +
        ‖v‖ * ‖qResidual - finiteHead N qResidual‖ :=
  reciprocal_head_dual_bound_of_orthogonal N qOne qResidual v
    (Submodule.inner_right_of_mem_orthogonal hv qResidual_mem_orthogonal)

/-- Weighted Cauchy--Schwarz in scalar form, without division by alpha. -/
theorem weighted_two_term_bound (a e b m t α : ℝ)
    (hα : 0 ≤ α)
    (h : |a| ≤ e * b + m * t) :
    α * a ^ 2 ≤ (e ^ 2 + α * m ^ 2) * (α * b ^ 2 + t ^ 2) := by
  have hh : a ^ 2 ≤ (e * b + m * t) ^ 2 := by
    have hs := mul_self_le_mul_self (abs_nonneg a) h
    nlinarith [sq_abs a]
  have hhα := mul_le_mul_of_nonneg_left hh hα
  nlinarith [sq_nonneg (e * t - α * m * b)]

/-- A finite Tikhonov dual certificate for any target and orthogonal detector. -/
theorem tikhonov_finite_dual_bound_of_orthogonal (N : ℕ)
    (x r v : QHilbert) (hvr : inner ℝ v r = 0)
    (α : ℝ) (hα : 0 ≤ α) :
    α * (inner ℝ x (finiteHead N r)) ^ 2 ≤
      (‖B (x - v)‖ ^ 2 + α * ‖v‖ ^ 2) *
        (α * ‖inverseFiniteHead N r‖ ^ 2 +
          ‖r - finiteHead N r‖ ^ 2) := by
  exact weighted_two_term_bound _ _ _ _ _ _ hα
    (reciprocal_head_dual_bound_of_orthogonal N x r v hvr)

/-- A finite dual certificate for the complete Tikhonov objective. -/
theorem tikhonov_finite_dual_bound (N : ℕ) (v : QHilbert)
    (hv : v ∈ closure) (α : ℝ) (hα : 0 ≤ α) :
    α * (inner ℝ qOne (finiteHead N qResidual)) ^ 2 ≤
      (‖B (qOne - v)‖ ^ 2 + α * ‖v‖ ^ 2) *
        (α * ‖inverseFiniteHead N qResidual‖ ^ 2 +
          ‖qResidual - finiteHead N qResidual‖ ^ 2) :=
  tikhonov_finite_dual_bound_of_orthogonal N qOne qResidual v
    (Submodule.inner_right_of_mem_orthogonal hv qResidual_mem_orthogonal) α hα

/-- Complete Q normal equations give the exact reciprocal Tikhonov remainder.
The same generic theorem applies to each finite legal dictionary. No bound
uniform in the regularization parameter is supplied by this identity. -/
theorem full_tikhonov_remainder (α : ℝ) (w : QHilbert) (hw : w ∈ closure)
    (hn : ∀ u ∈ closure,
      inner ℝ (B w - B qOne) (B u) + α * inner ℝ w u = 0)
    (v : QHilbert) (hv : v ∈ closure) :
    ‖B v - B qOne‖ ^ 2 + α * ‖v‖ ^ 2 =
      (‖B w - B qOne‖ ^ 2 + α * ‖w‖ ^ 2) +
        ‖B (v - w)‖ ^ 2 + α * ‖v - w‖ ^ 2 := by
  simpa only [RiemannResearch.Analysis.TikhonovQuadratic.objective] using
    RiemannResearch.Analysis.TikhonovQuadratic.objective_remainder_on_submodule
      closure B (B qOne) α w hw hn v hv

end RiemannResearch.RH.QReciprocalDualCertificate
