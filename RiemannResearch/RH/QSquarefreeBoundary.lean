/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.MobiusDifferenceCLM
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Properness and boundary of the squarefree Q-Hilbert closed span

Source: the user's CRT and weak compactness discussion, 25 October 2026.
The four-site functional is the existing omitted Möbius coordinate at 4,
with sign chosen to match f(4)-f(3)-f(2)+f(1). Its vanishing on the squarefree
closure excludes g_4 but does not exclude qOne. The boundary is the entire
proper closed subspace and is not norm compact.
-/

noncomputable section
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeBoundary
open ZetaTwoHilbert ZetaTwoOptimizerStage SquarefreeMobiusProjection
open RiemannResearch.Analysis.ExhaustiveWalk

private theorem not_squarefree_four : ¬ Squarefree (4 : ℕ) := by
  intro h
  have hh := Nat.squarefree_iff_prime_squarefree.mp h 2 Nat.prime_two
  norm_num at hh

/-- The explicit continuous four-site functional from the discussion. -/
def fourSiteFunctional : QHilbert →L[ℝ] ℝ := -qCoefficientCLM 4

theorem fourSiteFunctional_apply (f : QHilbert) :
    fourSiteFunctional f = qSequence f 4 - qSequence f 3 - qSequence f 2 +
      qSequence f 1 := by
  change -(-Pareto.mobiusDifferenceCLM 4 (ZetaTwoParetoTransfer.toPareto f)) = _
  rw [neg_neg, Pareto.mobiusDifferenceCLM_apply, ZetaTwoParetoTransfer.toPareto_sequence]
  have hd : (4 : ℕ).divisors = {1, 2, 4} := by decide
  rw [Pareto.mobiusDifference, hd]
  norm_num [ArithmeticFunction.moebius_eq_zero_of_not_squarefree not_squarefree_four,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

theorem fourSiteFunctional_zero_on_closure {f : QHilbert}
    (hf : f ∈ ZetaTwoOptimizerStage.closure) : fourSiteFunctional f = 0 := by
  have h : qCoefficientCLM 4 f = 0 := q_omitted_coordinate_zero 2 not_squarefree_four hf
  change -(qCoefficientCLM 4 f) = 0
  rw [h, neg_zero]

theorem fourSiteFunctional_qResidue_four : fourSiteFunctional (qResidue 4) = -1 := by
  have h := q_coordinate_biorthogonal 2 2
  norm_num at h
  change -(qCoefficientCLM 4 (qResidue 4)) = -1
  rw [h]

theorem fourSiteFunctional_qOne : fourSiteFunctional qOne = 0 := by
  rw [fourSiteFunctional_apply, qSequence_qOne]
  norm_num [qOneSequence]

theorem qResidue_four_not_mem : qResidue 4 ∉ ZetaTwoOptimizerStage.closure := by
  intro h
  have hz := fourSiteFunctional_zero_on_closure h
  rw [fourSiteFunctional_qResidue_four] at hz
  norm_num at hz

theorem closure_ne_top : ZetaTwoOptimizerStage.closure ≠ ⊤ := by
  intro h
  apply qResidue_four_not_mem
  rw [h]
  trivial

theorem closure_isClosed : IsClosed (ZetaTwoOptimizerStage.closure : Set QHilbert) := by
  exact (Submodule.span ℝ (Set.range squarefreeAtom)).isClosed_topologicalClosure

theorem closure_interior_eq_empty :
    interior (ZetaTwoOptimizerStage.closure : Set QHilbert) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  exact closure_ne_top (Submodule.eq_top_of_nonempty_interior'
    ZetaTwoOptimizerStage.closure ⟨x, hx⟩)

theorem closure_frontier_eq_self :
    frontier (ZetaTwoOptimizerStage.closure : Set QHilbert) =
      (ZetaTwoOptimizerStage.closure : Set QHilbert) := by
  rw [frontier, closure_isClosed.closure_eq, closure_interior_eq_empty, Set.sdiff_empty]

theorem qResidue_two_mem : qResidue 2 ∈ ZetaTwoOptimizerStage.closure := by
  apply (Submodule.span ℝ (Set.range squarefreeAtom)).le_topologicalClosure
  have hi : squarefreeAtom 0 = qResidue 2 := by
    simp [squarefreeAtom, Nat.prime_two.squarefree]
  rw [← hi]
  exact Submodule.subset_span ⟨0, rfl⟩

theorem qResidue_two_ne_zero : qResidue 2 ≠ 0 := by
  intro h
  have hb := q_coordinate_biorthogonal 0 0
  norm_num [h] at hb

theorem closure_not_isBounded :
    ¬ Bornology.IsBounded (ZetaTwoOptimizerStage.closure : Set QHilbert) := by
  intro hb
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
  have hn : 0 < ‖qResidue 2‖ := norm_pos_iff.mpr qResidue_two_ne_zero
  let c : ℝ := (|R| + 1) / ‖qResidue 2‖
  have hcpos : 0 < c := div_pos (by positivity) hn
  have hc := hR (c • qResidue 2)
    (ZetaTwoOptimizerStage.closure.smul_mem c qResidue_two_mem)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos] at hc
  have hv : c * ‖qResidue 2‖ = |R| + 1 := by
    dsimp [c]
    exact div_mul_cancel₀ _ (ne_of_gt hn)
  rw [hv] at hc
  linarith [le_abs_self R]

theorem closure_not_isCompact :
    ¬ IsCompact (ZetaTwoOptimizerStage.closure : Set QHilbert) :=
  fun h => closure_not_isBounded h.isBounded

theorem closure_frontier_not_isCompact :
    ¬ IsCompact (frontier (ZetaTwoOptimizerStage.closure : Set QHilbert)) := by
  rw [closure_frontier_eq_self]
  exact closure_not_isCompact

end RiemannResearch.RH.QSquarefreeBoundary
