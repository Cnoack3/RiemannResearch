/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.SingleDirectionResponseDifference
import RiemannResearch.RH.QShiftedReciprocalBessel
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability

/-!
# Finite variation budgets for orthonormal smoothed projection innovations

Source: the user's request to control actual squarefree corrections. This
reusable assembly retains explicit orthonormality and residual-energy bounds.
The canonical infinite-stage specialization is proved in the research note;
this module does not silently assert that specialization or an exponential bound.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QShiftedReciprocal
open ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis.SingleDirectionProjection

/-- Uniform finite variation over any orthonormal family of legal innovations.
Specializing to an actual nested walk still requires identifying its innovations. -/
theorem orthonormal_response_variation_budget {ι : Type*}
    (u : ι → QHilbert) (hu : Orthonormal ℝ u)
    (U : ι → Submodule ℝ QHilbert)
    [∀ i, (U i).HasOrthogonalProjection]
    [∀ i, (U i ⊔ Submodule.span ℝ ({u i} : Set QHilbert)).HasOrthogonalProjection]
    (hs : ∀ i, u i ∈ (U i)ᗮ)
    (f : QHilbert) (s : Finset ι) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ i ∈ s, ‖f - (U i).starProjection f‖^2 ≤ R) :
    (∑ i ∈ s,
      ‖responseOperator (U i ⊔ Submodule.span ℝ ({u i} : Set QHilbert)) B f -
        responseOperator (U i) B f‖^2) ≤ R * (zetaTwo - 1) := by
  classical
  calc
    _ ≤ ∑ i ∈ s, R * ‖B (u i)‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (response_extension_difference_norm_sq_le_unit
        (U i) (u i) (hs i) (hu.norm_eq_one i) B B_symmetric f).trans
        (mul_le_mul_of_nonneg_right (hr i hi) (sq_nonneg _))
    _ = R * ∑ i ∈ s, ‖B (u i)‖^2 := by rw [Finset.mul_sum]
    _ ≤ R * (zetaTwo - 1) :=
      mul_le_mul_of_nonneg_left (orthonormal_B_norm_sq_sum_le u hu s) hR

end RiemannResearch.RH.QShiftedReciprocal
