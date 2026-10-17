/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PrimitiveRegularization
import RiemannResearch.RH.QPhysicalDifference
import RiemannResearch.RH.QBoundedCoordinateClosure
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Physical Q primitive-energy closure and canonical regularized minimizers

Source: user-provided Squarefree_Primitive_Energy_Regularization_2026-10-17,
Sections 4, 6 and 9. Bagchi, https://arxiv.org/abs/math/0607733,
Remark 8, motivates squarefree constant closure. The forward implication
from RH to squarefree closure is a literature input, not formalized here.

The physical difference is bounded and injective in `QPhysicalDifference`.
Canonical squarefree minimizers exist uniquely, unconditionally. The exact
uniform O(penalty) budget is equivalent to squarefree constant closure.
The Mathlib RH consumer is a conditional research reduction: its complete
energy budget remains an Open arithmetic obligation.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QPrimitiveEnergyClosure
open ZetaTwoHilbert SquarefreeRadicalDifference

theorem coordinate_limits_of_difference_limits
    (F : ℕ → QHilbert) (x : QHilbert)
    (hdiff : ∀ k, 0 < k →
      Tendsto (fun N => qDifference (F N) k) atTop (𝓝 (qDifference x k))) :
    ∀ k, Tendsto (fun N => qSequence (F N) k) atTop (𝓝 (qSequence x k)) := by
  intro k
  induction k with
  | zero => simpa only [qSequence_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | succ k ih =>
    have h := (hdiff (k + 1) (by omega)).add ih
    simpa only [qDifference, Nat.add_sub_cancel, sub_add_cancel] using h

theorem mem_closure_of_bounded_difference_limits
    (S : Submodule ℝ QHilbert) (F : ℕ → QHilbert) (x : QHilbert)
    (hmem : ∀ N, F N ∈ S)
    (hdiff : ∀ k, 0 < k →
      Tendsto (fun N => qDifference (F N) k) atTop (𝓝 (qDifference x k)))
    {B : ℝ} (henergy : ∀ N, ‖F N‖ ^ 2 ≤ B) :
    x ∈ S.topologicalClosure := by
  apply QBoundedCoordinateClosure.mem_closure_of_bounded_coordinate_limits
    S F x hmem (fun k _ => coordinate_limits_of_difference_limits F x hdiff k)
    (C := B + 1)
  intro N
  nlinarith [henergy N, sq_nonneg (‖F N‖ - 1)]

end RiemannResearch.RH.QPrimitiveEnergyClosure



namespace RiemannResearch.RH.QPrimitiveEnergyClosure
open ZetaTwoHilbert SquarefreeRadicalDifference QPhysicalDifference

/-- Strong derivative convergence plus a full primitive-energy bound forces closure. -/
theorem mem_closure_of_bounded_derivative_limits
    (S : Submodule ℝ QHilbert) (F : ℕ → QHilbert) (x : QHilbert)
    (hmem : ∀ N, F N ∈ S)
    (hdiff : Tendsto (fun N => differenceCLM (F N)) atTop (𝓝 (differenceCLM x)))
    {B : ℝ} (henergy : ∀ N, ‖F N‖ ^ 2 ≤ B) :
    x ∈ S.topologicalClosure := by
  apply mem_closure_of_bounded_difference_limits S F x hmem _ henergy
  intro k _
  have h := ((continuous_qSequence k).tendsto (differenceCLM x)).comp hdiff
  simpa only [Function.comp_def, qSequence_differenceCLM] using h

/-- The O(penalty) objective budget supplies both hypotheses of bounded closure.
The budget is an explicit arithmetic assumption, not an unconditional estimate. -/
theorem mem_closure_of_regularized_budget
    (S : Submodule ℝ QHilbert) (F : ℕ → QHilbert) (x : QHilbert)
    (hmem : ∀ N, F N ∈ S) (penalty : ℕ → ℝ)
    (hpos : ∀ N, 0 < penalty N) (hzero : Tendsto penalty atTop (𝓝 0))
    {C : ℝ} (hbudget : ∀ N,
      ‖differenceCLM (F N) - differenceCLM x‖ ^ 2 + penalty N * ‖F N‖ ^ 2 ≤
        C * penalty N) : x ∈ S.topologicalClosure := by
  have henergy (N : ℕ) : ‖F N‖ ^ 2 ≤ C := by
    have h := hbudget N
    nlinarith [sq_nonneg ‖differenceCLM (F N) - differenceCLM x‖, hpos N]
  have hderivative (N : ℕ) :
      ‖differenceCLM (F N) - differenceCLM x‖ ^ 2 ≤ C * penalty N := by
    have h := hbudget N
    have hp := mul_nonneg (hpos N).le (sq_nonneg ‖F N‖)
    linarith
  have hsq : Tendsto (fun N => ‖differenceCLM (F N) - differenceCLM x‖ ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) hderivative
    simpa using hzero.const_mul C
  have hn : Tendsto (fun N => ‖differenceCLM (F N) - differenceCLM x‖)
      atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h
  apply mem_closure_of_bounded_derivative_limits S F x hmem _ henergy
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- Actual RH consumer. Its complete regularized energy budget remains Open. -/
theorem riemannHypothesis_of_regularized_legal_budget
    (F : ℕ → QHilbert)
    (hmem : ∀ N, F N ∈ QFullResidueProjection.legalSpan)
    (penalty : ℕ → ℝ) (hpos : ∀ N, 0 < penalty N)
    (hzero : Tendsto penalty atTop (𝓝 0))
    {C : ℝ} (hbudget : ∀ N,
      ‖differenceCLM (F N) - differenceCLM qOne‖ ^ 2 + penalty N * ‖F N‖ ^ 2 ≤
        C * penalty N) : RiemannHypothesis := by
  apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
  exact mem_closure_of_regularized_budget QFullResidueProjection.legalSpan
    F qOne hmem penalty hpos hzero hbudget

end RiemannResearch.RH.QPrimitiveEnergyClosure


namespace RiemannResearch.RH.QPrimitiveEnergyClosure
open ZetaTwoHilbert ZetaTwoProbability SquarefreeRadicalDifference QPhysicalDifference
open RiemannResearch.Analysis.PrimitiveRegularization

abbrev SquarefreeSpace := qSquarefreeCRTSpan.topologicalClosure

def squarefreeDifference : SquarefreeSpace →L[ℝ] QHilbert :=
  differenceCLM.comp SquarefreeSpace.subtypeL

/-- The canonical physical squarefree regularized minimizer exists unconditionally. -/
theorem exists_unique_squarefree_minimizer {lam : ℝ} (hlam : 0 < lam) :
    ∃! u : SquarefreeSpace, ∀ v : SquarefreeSpace,
      ‖differenceCLM (u : QHilbert) - differenceCLM qOne‖ ^ 2 +
        lam * ‖(u : QHilbert)‖ ^ 2 ≤
      ‖differenceCLM (v : QHilbert) - differenceCLM qOne‖ ^ 2 +
        lam * ‖(v : QHilbert)‖ ^ 2 := by
  let : CompleteSpace SquarefreeSpace :=
    qSquarefreeCRTSpan.isClosed_topologicalClosure.completeSpace_coe
  exact exists_unique_minimizer squarefreeDifference (differenceCLM qOne) hlam

/-- For actual squarefree normal solutions, the uniform critical budget is
exactly equivalent to constant closure. No arithmetic budget is supplied. -/
theorem squarefree_constant_mem_iff_regularized_budget
    (F : ℕ → SquarefreeSpace) (penalty : ℕ → ℝ)
    (hpos : ∀ N, 0 < penalty N) (hzero : Tendsto penalty atTop (𝓝 0))
    (hnormal : ∀ N, IsNormal squarefreeDifference.toLinearMap ⊤
      (differenceCLM qOne) (penalty N) (F N)) :
    qOne ∈ SquarefreeSpace ↔ ∃ C : ℝ, ∀ N,
      ‖differenceCLM (F N : QHilbert) - differenceCLM qOne‖ ^ 2 +
        penalty N * ‖(F N : QHilbert)‖ ^ 2 ≤ C * penalty N := by
  constructor
  · intro hOne
    refine ⟨1, ?_⟩
    intro N
    have h := normal_minimizes squarefreeDifference.toLinearMap ⊤
      (differenceCLM qOne) (penalty N) (F N) ⟨qOne, hOne⟩
      (by simp) (by simp) (hpos N).le (hnormal N)
    simpa only [squarefreeDifference, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, sub_self, norm_zero,
      zero_pow (by decide : 2 ≠ 0), zero_add, Submodule.coe_norm,
      qOne_norm_sq, mul_one, one_mul] using h
  · rintro ⟨C, hbudget⟩
    have h := mem_closure_of_regularized_budget SquarefreeSpace
      (fun N => (F N : QHilbert)) qOne (fun N => (F N).property)
      penalty hpos hzero hbudget
    change qOne ∈ closure (SquarefreeSpace : Set QHilbert) at h
    rw [qSquarefreeCRTSpan.isClosed_topologicalClosure.closure_eq] at h
    exact h

end RiemannResearch.RH.QPrimitiveEnergyClosure
