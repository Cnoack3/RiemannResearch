/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QL1Equality
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.NormNum

/-!
# L1/L2 equality for the actual squarefree limiting projection

Source: the user's norm-equality discussion, 25 October 2026.
For a general physical vector, equality of L1 and L2 means constant absolute
value, not constant signed value. For the actual squarefree projection and
its residual, the established tail criterion makes even constant absolute
value sufficient to identify the projection with the constant target.
These are conditional research reductions: equality itself remains Open.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeNormEquality
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeResidualTail

private theorem bounded_of_constant_absolute (f : QHilbert)
    (h : ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ, 0 < n → |qSequence f n| = c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |qSequence f n| ≤ C := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, ?_⟩
  intro n
  cases n with
  | zero => simpa only [qSequence_zero, abs_zero] using hc
  | succ n => exact (h (n + 1) (Nat.succ_pos n)).le

/-- L1/L2 equality for the actual limiting residual is equivalent to its vanishing.
No equality hypothesis is asserted to hold. -/
theorem limitingResidual_l1_eq_norm_iff_zero :
    qL1 limitingResidual = ‖limitingResidual‖ ↔ limitingResidual = 0 := by
  constructor
  · intro h
    apply limitingResidual_eq_zero_iff_physically_bounded.mpr
    exact bounded_of_constant_absolute limitingResidual
      ((qL1_eq_norm_iff_abs_constant limitingResidual).mp h)
  · intro hr
    have hz : qL1 (0 : QHilbert) = 0 :=
      le_antisymm (by simpa only [norm_zero] using qL1_le_norm (0 : QHilbert))
        (qL1_nonneg 0)
    simpa only [hr, norm_zero] using hz

/-- The same saturation criterion for the actual limiting projection. -/
theorem limitingProjection_l1_eq_norm_iff_one :
    qL1 (closure.starProjection qOne) = ‖closure.starProjection qOne‖ ↔
      closure.starProjection qOne = qOne := by
  constructor
  · intro h
    apply limitingProjection_eq_one_iff_physically_bounded.mpr
    exact bounded_of_constant_absolute (closure.starProjection qOne)
      ((qL1_eq_norm_iff_abs_constant (closure.starProjection qOne)).mp h)
  · intro hF
    rw [hF]
    apply (qL1_eq_norm_iff_abs_constant qOne).mpr
    refine ⟨1, by norm_num, ?_⟩
    intro n hn
    rw [qSequence_qOne]
    simp [qOneSequence, Nat.ne_of_gt hn]

/-- In the nonzero-residual case, the L1/L2 inequality is genuinely strict. -/
theorem limitingResidual_l1_lt_norm (hr : limitingResidual ≠ 0) :
    qL1 limitingResidual < ‖limitingResidual‖ := by
  have hle := qL1_le_norm limitingResidual
  have hne : qL1 limitingResidual ≠ ‖limitingResidual‖ :=
    fun h => hr (limitingResidual_l1_eq_norm_iff_zero.mp h)
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact (hne h).elim

/-- A strict projection has a strict L1/L2 gap, even though both moments converge. -/
theorem limitingProjection_l1_lt_norm (hF : closure.starProjection qOne ≠ qOne) :
    qL1 (closure.starProjection qOne) < ‖closure.starProjection qOne‖ := by
  have hle := qL1_le_norm (closure.starProjection qOne)
  have hne : qL1 (closure.starProjection qOne) ≠ ‖closure.starProjection qOne‖ :=
    fun h => hF (limitingProjection_l1_eq_norm_iff_one.mp h)
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact (hne h).elim

end RiemannResearch.RH.QSquarefreeNormEquality
