/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QHeadProjectedResidual
import RiemannResearch.RH.QFullReciprocalHeadCompletion
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Asymptotic obstruction for actual reciprocal-head repairs

Source: the user-provided reciprocal-head investigation, 7 November 2026,
Section 6. The eventual lower estimate is the division-free, extended-liminf
meaning of the paper's lower bound. It also applies when repair norms are
unbounded; no real-valued liminf boundedness convention is needed.
The existing code name QShiftedReciprocal.B denotes the multiplier called R
in the discussion, not the density dQ/dP.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QFullReciprocalHeadCompletion
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QFiniteSupportDualCriterion QFullDisplacement QFullResidueProjection

/-- The signed finite-head numerator converges to the actual Pareto energy. -/
theorem reciprocal_head_numerator_tendsto :
    Tendsto (fun N => inner ℝ qResidual
      (finiteHead N (QShiftedReciprocal.B displacement))) atTop
      (𝓝 (‖toPareto displacement‖ ^ 2 / zetaTwo)) := by
  have h : Tendsto (fun N => inner ℝ qResidual
      (finiteHead N (QShiftedReciprocal.B displacement))) atTop
      (𝓝 (inner ℝ qResidual (QShiftedReciprocal.B displacement))) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => qResidual) atTop (𝓝 qResidual)).inner
        (finiteHead_tendsto (QShiftedReciprocal.B displacement))
  have he : inner ℝ qResidual (QShiftedReciprocal.B displacement) =
      ‖toPareto displacement‖ ^ 2 / zetaTwo := by
    apply (eq_div_iff (ne_of_gt zetaTwo_pos)).mpr
    have hi : inner ℝ qResidual (QShiftedReciprocal.B displacement) =
        inner ℝ displacement (QShiftedReciprocal.B qResidual) := by
      rw [← QShiftedReciprocal.B_symmetric, real_inner_comm]
    rw [hi, mul_comm]
    exact displacement_p_energy.symm
  simpa only [he] using h

/-- The projected-head version of the sharp actual-target pairing bound. -/
theorem reciprocal_head_projected_pairing_bound (N : ℕ) (F : QHilbert)
    (hF : F ∈ closure)
    (hh : ∀ n < N, F n = QShiftedReciprocal.B displacement n) :
    |inner ℝ qResidual (finiteHead N (QShiftedReciprocal.B displacement))| ≤
      ‖F‖ * ‖closure.starProjection (finiteHead N qResidual)‖ :=
  matching_head_projected_pairing_bound closure N
    (QShiftedReciprocal.B displacement) F qResidual hF hh

theorem reciprocal_projected_head_norm_le_tail (N : ℕ) :
    ‖closure.starProjection (finiteHead N qResidual)‖ ≤
      ‖qResidual - finiteHead N qResidual‖ :=
  projected_residual_head_norm_le closure N qResidual qResidual_mem_orthogonal

/-- Every exact legal repair has asymptotic norm-tail product at least the
Pareto displacement energy divided by zeta(2). -/
theorem reciprocal_head_product_eventually_lower
    {F : ℕ → QHilbert} (hF : ∀ N, F N ∈ closure)
    (hh : ∀ N n, n < N → F N n = QShiftedReciprocal.B displacement n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ‖toPareto displacement‖ ^ 2 / zetaTwo - ε <
      ‖F N‖ * ‖qResidual - finiteHead N qResidual‖ := by
  have hlim := (tendsto_order.1 reciprocal_head_numerator_tendsto).1
    (‖toPareto displacement‖ ^ 2 / zetaTwo - ε)
    (sub_lt_self _ hε)
  filter_upwards [hlim] with N hN
  apply hN.trans_le
  apply (le_abs_self _).trans
  apply matching_head_complete_pairing_bound N
    (QShiftedReciprocal.B displacement) (F N) qResidual _ (hh N)
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal (hF N) qResidual_mem_orthogonal

/-- The stronger projected denominator has the same asymptotic lower barrier. -/
theorem reciprocal_head_projected_product_eventually_lower
    {F : ℕ → QHilbert} (hF : ∀ N, F N ∈ closure)
    (hh : ∀ N n, n < N → F N n = QShiftedReciprocal.B displacement n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ‖toPareto displacement‖ ^ 2 / zetaTwo - ε <
      ‖F N‖ * ‖closure.starProjection (finiteHead N qResidual)‖ := by
  have hlim := (tendsto_order.1 reciprocal_head_numerator_tendsto).1
    (‖toPareto displacement‖ ^ 2 / zetaTwo - ε)
    (sub_lt_self _ hε)
  filter_upwards [hlim] with N hN
  exact hN.trans_le ((le_abs_self _).trans
    (reciprocal_head_projected_pairing_bound N (F N) (hF N) (hh N)))

end RiemannResearch.RH.QFullReciprocalHeadCompletion
