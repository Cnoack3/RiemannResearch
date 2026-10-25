/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeResidualTail

/-!
# Rigidity of a common squarefree projection under Q and Pareto

Source: the user's proposed change-of-measure contradiction, 25 October 2026.
The Pareto space below is exactly the image of the closed squarefree space,
not the larger closed span of all conductors. Equivalent norms preserve this
closed span but do not identify its two orthogonal projections.

For this particular dictionary, a common projection would force the residual
to vanish. The arithmetic input is that a bounded squarefree annihilator has
mean zero. The change of law makes r/(n+1) a second annihilator when the two
projections agree; its positive energy then forces r = 0. Agreement itself is
not proved, so these results do not establish the target closure statement.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QSquarefreeMeasureRigidity
open Pareto ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer
open QParetoEquivalence QShiftedReciprocal QSquarefreeResidualTail

/-- The Pareto realization of the same closed squarefree physical span. -/
def paretoSquarefreeClosure : Submodule ℝ ThresholdHilbert :=
  (ZetaTwoOptimizerStage.closure.map paretoEquiv.toLinearMap).topologicalClosure

instance paretoSquarefreeClosure_hasOrthogonalProjection :
    paretoSquarefreeClosure.HasOrthogonalProjection := by
  unfold paretoSquarefreeClosure
  infer_instance

theorem toPareto_mem_paretoSquarefreeClosure (f : QHilbert)
    (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    toPareto f ∈ paretoSquarefreeClosure := by
  apply Submodule.le_topologicalClosure
  exact ⟨f, hf, rfl⟩

/-- Both closed spaces have precisely the same physical functions. -/
theorem toPareto_mem_paretoSquarefreeClosure_iff (f : QHilbert) :
    toPareto f ∈ paretoSquarefreeClosure ↔ f ∈ ZetaTwoOptimizerStage.closure := by
  have hc : ZetaTwoOptimizerStage.closure.topologicalClosure =
      ZetaTwoOptimizerStage.closure := by
    apply SetLike.coe_injective
    change _root_.closure (ZetaTwoOptimizerStage.closure : Set QHilbert) =
      (ZetaTwoOptimizerStage.closure : Set QHilbert)
    exact (show IsClosed (ZetaTwoOptimizerStage.closure : Set QHilbert) from
      (Submodule.span ℝ
        (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).isClosed_topologicalClosure).closure_eq
  simpa only [paretoSquarefreeClosure, hc] using
    mem_closure_map_iff ZetaTwoOptimizerStage.closure f

/-- The bounded positive test B r = r/(n+1) remains a squarefree annihilator
exactly when the actual projection residual is zero. -/
theorem shiftedResidual_mem_orthogonal_iff :
    B ZetaTwoOptimizerStage.limitingResidual ∈
        ZetaTwoOptimizerStage.closureᗮ ↔
      ZetaTwoOptimizerStage.limitingResidual = 0 := by
  constructor
  · intro ho
    obtain ⟨C, hb⟩ := B_physical_bounded ZetaTwoOptimizerStage.limitingResidual
    have hC : 0 ≤ C := (abs_nonneg _).trans (hb 0)
    exact limitingResidual_eq_zero_of_bounded_faithful_test B
      (fun u => B_faithful u) ho C hC hb
  · intro hr
    rw [hr, map_zero]
    exact ZetaTwoOptimizerStage.closure.orthogonal.zero_mem

/-- Extra Pareto orthogonality of the actual Q residual would be enough.
Neither equivalence of norms nor change of measure supplies this hypothesis. -/
theorem limitingResidual_eq_zero_of_pareto_orthogonal
    (hp : ∀ v : QHilbert, v ∈ ZetaTwoOptimizerStage.closure →
      inner ℝ (toPareto v)
        (toPareto ZetaTwoOptimizerStage.limitingResidual) = 0) :
    ZetaTwoOptimizerStage.limitingResidual = 0 := by
  apply shiftedResidual_mem_orthogonal_iff.mp
  apply (ZetaTwoOptimizerStage.closure.mem_orthogonal _).mpr
  intro v hv
  have hq := Submodule.inner_right_of_mem_orthogonal hv
    limitingResidual_mem_squarefree_orthogonal
  have h := hp v hv
  rw [pareto_inner_identity, hq, zero_sub] at h
  exact neg_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (ne_of_gt zetaTwo_pos))

/-- The physical Q and Pareto projections agree if and only if the squarefree
target-membership problem has a positive answer. This is a reduction, not an
unconditional proof that the projections agree. -/
theorem projections_agree_iff_limitingResidual_eq_zero :
    toPareto (ZetaTwoOptimizerStage.closure.starProjection qOne) =
        paretoSquarefreeClosure.starProjection hilbertOne ↔
      ZetaTwoOptimizerStage.limitingResidual = 0 := by
  constructor
  · intro hp
    have hr : toPareto ZetaTwoOptimizerStage.limitingResidual =
        hilbertOne - paretoSquarefreeClosure.starProjection hilbertOne := by
      change toParetoLinear
        (qOne - ZetaTwoOptimizerStage.closure.starProjection qOne) = _
      rw [map_sub]
      change toPareto qOne -
        toPareto (ZetaTwoOptimizerStage.closure.starProjection qOne) = _
      rw [toPareto_qOne, hp]
    apply limitingResidual_eq_zero_of_pareto_orthogonal
    intro v hv
    rw [hr]
    exact Submodule.inner_right_of_mem_orthogonal
      (toPareto_mem_paretoSquarefreeClosure v hv)
      (Submodule.sub_starProjection_mem_orthogonal
        (K := paretoSquarefreeClosure) hilbertOne)
  · intro hr
    have hq : ZetaTwoOptimizerStage.closure.starProjection qOne = qOne :=
      (sub_eq_zero.mp hr).symm
    have hmem : hilbertOne ∈ paretoSquarefreeClosure := by
      rw [← toPareto_qOne]
      apply toPareto_mem_paretoSquarefreeClosure
      rw [← hq]
      exact ZetaTwoOptimizerStage.closure.starProjection_apply_mem qOne
    have hp : paretoSquarefreeClosure.starProjection hilbertOne = hilbertOne :=
      Submodule.starProjection_eq_self_iff.mpr hmem
    rw [hq, toPareto_qOne, hp]

theorem projections_agree_iff_one_mem_squarefreeClosure :
    toPareto (ZetaTwoOptimizerStage.closure.starProjection qOne) =
        paretoSquarefreeClosure.starProjection hilbertOne ↔
      qOne ∈ ZetaTwoOptimizerStage.closure := by
  rw [projections_agree_iff_limitingResidual_eq_zero]
  change qOne - ZetaTwoOptimizerStage.closure.starProjection qOne = 0 ↔ _
  rw [sub_eq_zero, eq_comm]
  exact Submodule.starProjection_eq_self_iff

/-- A strict squarefree projection necessarily changes under this change of law. -/
theorem projections_differ_of_limitingResidual_ne_zero
    (hr : ZetaTwoOptimizerStage.limitingResidual ≠ 0) :
    toPareto (ZetaTwoOptimizerStage.closure.starProjection qOne) ≠
      paretoSquarefreeClosure.starProjection hilbertOne := by
  exact fun hp => hr (projections_agree_iff_limitingResidual_eq_zero.mp hp)


/-- A fixed Q optimizer sequence keeps its physical limit under change of measure. -/
theorem qOptimizers_tendsto_pareto_realization :
    Tendsto (fun M => toPareto (ZetaTwoOptimizerStage.optimizer M)) atTop
      (𝓝 (toPareto (ZetaTwoOptimizerStage.closure.starProjection qOne))) :=
  (tendsto_toPareto_iff _ _).mpr ZetaTwoOptimizerStage.optimizer_tendsto

/-- Convergence to the other metric's optimizer is exactly the unresolved
zero-residual condition; it does not follow just from equivalent norms. -/
theorem qOptimizers_tendsto_paretoProjection_iff :
    Tendsto (fun M => toPareto (ZetaTwoOptimizerStage.optimizer M)) atTop
        (𝓝 (paretoSquarefreeClosure.starProjection hilbertOne)) ↔
      ZetaTwoOptimizerStage.limitingResidual = 0 := by
  constructor
  · intro h
    apply projections_agree_iff_limitingResidual_eq_zero.mp
    exact tendsto_nhds_unique qOptimizers_tendsto_pareto_realization h
  · intro hr
    have h := projections_agree_iff_limitingResidual_eq_zero.mpr hr
    simpa only [h] using qOptimizers_tendsto_pareto_realization

end RiemannResearch.RH.QSquarefreeMeasureRigidity
