/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFullCofinalHarmonic
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact reciprocal-head error paired with the actual residual tail

Source: the user's weak-star compactness request and
CrossedDistanceLeanHandoff20261106.md, 6 November 2026.
The signed identity specializes the already checked displacement energy.
Finite head agreement kills exactly the head pairing; legality kills exactly
the full residual pairing. The remaining complete error and residual tail
are retained. Their product tending to zero suffices for RH and does not
require a uniformly bounded correction family. This decay provider is Open.
The related squarefree constant-target strategy
is in QSquarefreeExactHeadResidualBarrier; here the target is the actual
full-conductor reciprocal displacement. No mathematical priority is claimed.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QFullReciprocalHeadTail
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QShiftedReciprocal
open QFullResidueProjection QFullDisplacement QFiniteSupportDualCriterion

/-- The exact finite-head elimination identity, before either factor is estimated. -/
theorem reciprocal_head_energy_identity (N : ℕ) (F : QHilbert)
    (hF : F ∈ closure) (hhead : ∀ n < N, F n = B displacement n) :
    ‖toPareto displacement‖ ^ 2 =
      zetaTwo * inner ℝ (B displacement - F) (qResidual - finiteHead N qResidual) := by
  have hlegal : inner ℝ F qResidual = 0 :=
    Submodule.inner_right_of_mem_orthogonal hF qResidual_mem_orthogonal
  have hzero : inner ℝ (B displacement - F) (finiteHead N qResidual) = 0 := by
    rw [inner_finiteHead_eq_sum]
    apply Finset.sum_eq_zero
    intro n hn
    change qResidual n * (B displacement n - F n) = 0
    rw [hhead n (Finset.mem_range.mp hn), sub_self, mul_zero]
  rw [inner_sub_right, hzero, sub_zero, inner_sub_left, hlegal, sub_zero, B_symmetric]
  exact displacement_p_energy

/-- The full reciprocal interpolation error is multiplied by the actual residual tail. -/
theorem reciprocal_head_energy_le_error_tail (N : ℕ) (F : QHilbert)
    (hF : F ∈ closure) (hhead : ∀ n < N, F n = B displacement n) :
    ‖toPareto displacement‖ ^ 2 ≤ zetaTwo *
      (‖B displacement - F‖ * ‖qResidual - finiteHead N qResidual‖) := by
  rw [reciprocal_head_energy_identity N F hF hhead]
  exact mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) zetaTwo_pos.le

/-- A directly usable norm-growth bound retaining the complete interpolation norm. -/
theorem reciprocal_head_energy_le_norm_tail (N : ℕ) (F : QHilbert)
    (hF : F ∈ closure) (hhead : ∀ n < N, F n = B displacement n) :
    ‖toPareto displacement‖ ^ 2 ≤ zetaTwo *
      ((‖B displacement‖ + ‖F‖) * ‖qResidual - finiteHead N qResidual‖) :=
  (reciprocal_head_energy_le_error_tail N F hF hhead).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)) zetaTwo_pos.le)

/-- Residual tails vanish independently of RH or legal-space membership. -/
theorem residual_tail_norm_tendsto_zero :
    Tendsto (fun N => ‖qResidual - finiteHead N qResidual‖) atTop (𝓝 0) := by
  simpa only [sub_self, norm_zero] using
    (tendsto_const_nhds.sub (finiteHead_tendsto qResidual) :
      Tendsto (fun N => qResidual - finiteHead N qResidual) atTop
        (𝓝 (qResidual - qResidual))).norm

/-- Product decay permits unbounded correction norms; boundedness is not a premise. -/
theorem displacement_eq_zero_of_error_tail_product
    {F : ℕ → QHilbert} (hF : ∀ N, F N ∈ closure)
    (hhead : ∀ N n, n < N → F N n = B displacement n)
    (hprod : Tendsto (fun N =>
      ‖B displacement - F N‖ * ‖qResidual - finiteHead N qResidual‖)
      atTop (𝓝 0)) : displacement = 0 := by
  have ht : Tendsto (fun N => zetaTwo *
      (‖B displacement - F N‖ * ‖qResidual - finiteHead N qResidual‖))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hprod.const_mul zetaTwo
  by_contra hd
  have hpq : 0 < zetaTwo * ‖displacement‖ ^ 2 :=
    mul_pos zetaTwo_pos (sq_pos_of_pos (norm_pos_iff.mpr hd))
  have hmetric := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq displacement
  have hp : 0 < ‖toPareto displacement‖ ^ 2 := by nlinarith
  obtain ⟨N, hN⟩ := ((tendsto_order.1 ht).2 _ hp).exists
  exact (not_lt_of_ge
    (reciprocal_head_energy_le_error_tail N (F N) (hF N) (hhead N))) hN

/-- It is enough that the repair norm grows slower than the inverse residual-tail norm. -/
theorem displacement_eq_zero_of_repair_norm_tail_product
    {F : ℕ → QHilbert} (hF : ∀ N, F N ∈ closure)
    (hhead : ∀ N n, n < N → F N n = B displacement n)
    (hprod : Tendsto (fun N => ‖F N‖ * ‖qResidual - finiteHead N qResidual‖)
      atTop (𝓝 0)) : displacement = 0 := by
  apply displacement_eq_zero_of_error_tail_product hF hhead
  refine squeeze_zero (fun N => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun N => mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)) ?_
  have ht := (residual_tail_norm_tendsto_zero.const_mul ‖B displacement‖).add hprod
  simpa only [add_mul, mul_zero, zero_add] using ht

/-- Conditional RH reduction with a complete error-tail product provider. -/
theorem riemannHypothesis_of_error_tail_product
    {F : ℕ → QHilbert} (hF : ∀ N, F N ∈ closure)
    (hhead : ∀ N n, n < N → F N n = B displacement n)
    (hprod : Tendsto (fun N =>
      ‖B displacement - F N‖ * ‖qResidual - finiteHead N qResidual‖)
      atTop (𝓝 0)) : RiemannHypothesis :=
  QFullDisplacement.riemannHypothesis_of_displacement_eq_zero
    (displacement_eq_zero_of_error_tail_product hF hhead hprod)

/-- Conditional RH reduction allowing growth of the interpolation norm. -/
theorem riemannHypothesis_of_repair_norm_tail_product
    {F : ℕ → QHilbert} (hF : ∀ N, F N ∈ closure)
    (hhead : ∀ N n, n < N → F N n = B displacement n)
    (hprod : Tendsto (fun N => ‖F N‖ * ‖qResidual - finiteHead N qResidual‖)
      atTop (𝓝 0)) : RiemannHypothesis :=
  QFullDisplacement.riemannHypothesis_of_displacement_eq_zero
    (displacement_eq_zero_of_repair_norm_tail_product hF hhead hprod)

/-- A nonzero full-conductor displacement has positive Pareto energy. -/
theorem displacement_p_energy_pos (hd : displacement ≠ 0) :
    0 < ‖toPareto displacement‖ ^ 2 := by
  have hp : 0 < zetaTwo * ‖displacement‖ ^ 2 :=
    mul_pos zetaTwo_pos (sq_pos_of_pos (norm_pos_iff.mpr hd))
  have hmetric := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq displacement
  nlinarith

/-- The denominator cannot vanish when a legal repair exists and d is nonzero. -/
theorem residual_tail_norm_pos_of_head_repair (hd : displacement ≠ 0)
    (N : ℕ) (F : QHilbert) (hF : F ∈ closure)
    (hhead : ∀ n < N, F n = B displacement n) :
    0 < ‖qResidual - finiteHead N qResidual‖ := by
  have hp := displacement_p_energy_pos hd
  have he := reciprocal_head_energy_le_norm_tail N F hF hhead
  by_contra hn
  have hz : ‖qResidual - finiteHead N qResidual‖ = 0 :=
    le_antisymm (le_of_not_gt hn) (norm_nonneg _)
  rw [hz, mul_zero, mul_zero] at he
  exact (not_le_of_gt hp) he

/-- An explicit lower bound for the complete interpolation error. -/
theorem reciprocal_head_error_lower (hd : displacement ≠ 0)
    (N : ℕ) (F : QHilbert) (hF : F ∈ closure)
    (hhead : ∀ n < N, F n = B displacement n) :
    ‖toPareto displacement‖ ^ 2 /
      (zetaTwo * ‖qResidual - finiteHead N qResidual‖) ≤ ‖B displacement - F‖ := by
  have ht := residual_tail_norm_pos_of_head_repair hd N F hF hhead
  apply (div_le_iff₀ (mul_pos zetaTwo_pos ht)).mpr
  calc
    _ ≤ zetaTwo * (‖B displacement - F‖ * ‖qResidual - finiteHead N qResidual‖) :=
      reciprocal_head_energy_le_error_tail N F hF hhead
    _ = ‖B displacement - F‖ *
        (zetaTwo * ‖qResidual - finiteHead N qResidual‖) := by ring

/-- Every legal head repair incurs this inverse-residual-tail norm cost. -/
theorem reciprocal_head_norm_lower (hd : displacement ≠ 0)
    (N : ℕ) (F : QHilbert) (hF : F ∈ closure)
    (hhead : ∀ n < N, F n = B displacement n) :
    ‖toPareto displacement‖ ^ 2 /
        (zetaTwo * ‖qResidual - finiteHead N qResidual‖) - ‖B displacement‖ ≤ ‖F‖ := by
  have he := reciprocal_head_error_lower hd N F hF hhead
  have htri := norm_sub_le (B displacement) F
  linarith


end RiemannResearch.RH.QFullReciprocalHeadTail
