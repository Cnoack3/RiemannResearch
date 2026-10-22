/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QExactHeadAverages
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.PrimePowerTargetMellin
import Mathlib.Tactic.NormNum
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.PrimePowerTwoTargetCriterion

/-!
# Exact-head characterization of the two-prime target obligations

Source: user-provided two-prime Mellin/parity handoff, 20 October 2026,
Section 8.B.

The head repair comes from the existing finite-observation section theorem.
All approximants below are finite squarefree combinations, with a real constant
allowed only in `finiteWithConstants`. The converse allows the conductor support
to depend on the requested head; it does not bound a prescribed cutoff schedule.
The uniform complete-Q energy estimates remain open.
-/

noncomputable section
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability

/-- The algebraic dictionary of finite squarefree legal combinations plus constants. -/
def finiteWithConstants : Submodule ℝ QHilbert :=
  qSquarefreeCRTSpan ⊔ Submodule.span ℝ {qOne}

/-- Closing before or after adjoining the one-dimensional constant space
gives the same actual complete-Q target space. -/
theorem finiteWithConstants_closure :
    finiteWithConstants.topologicalClosure = closureWithConstants := by
  let K : Submodule ℝ QHilbert := Submodule.span ℝ {qOne}
  change (qSquarefreeCRTSpan ⊔ K).topologicalClosure =
    (ZetaTwoOptimizerStage.closure ⊔ K).topologicalClosure
  apply le_antisymm
  · apply (qSquarefreeCRTSpan ⊔ K).topologicalClosure_minimal _
      (ZetaTwoOptimizerStage.closure ⊔ K).isClosed_topologicalClosure
    apply le_trans (sup_le_sup ?_ le_rfl)
      (ZetaTwoOptimizerStage.closure ⊔ K).le_topologicalClosure
    rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
    exact qSquarefreeCRTSpan.le_topologicalClosure
  · apply (ZetaTwoOptimizerStage.closure ⊔ K).topologicalClosure_minimal _
      (qSquarefreeCRTSpan ⊔ K).isClosed_topologicalClosure
    refine sup_le ?_ (le_trans le_sup_right (qSquarefreeCRTSpan ⊔ K).le_topologicalClosure)
    rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
    exact qSquarefreeCRTSpan.topologicalClosure_minimal
      (le_trans le_sup_left (qSquarefreeCRTSpan ⊔ K).le_topologicalClosure)
      (qSquarefreeCRTSpan ⊔ K).isClosed_topologicalClosure

/-- Each prime-power target obligation is exactly a bounded full-energy
finite interpolation problem. No target membership is supplied by this equivalence. -/
theorem qTarget_mem_closureWithConstants_iff_bounded_exact_heads
    (p : ℕ) (hp : 1 < p) :
    qTarget p hp ∈ closureWithConstants ↔
      ∃ B : ℝ, ∀ M : ℕ, ∃ g : QHilbert, g ∈ finiteWithConstants ∧
        (∀ n, 0 < n → n ≤ M → qSequence g n = (Nat.log p n : ℝ)) ∧
        ‖g‖ ^ 2 ≤ B := by
  rw [← finiteWithConstants_closure]
  simpa only [qTarget_sequence] using
    QExactHeadAverages.mem_closure_iff_bounded_target_heads finiteWithConstants (qTarget p hp)

/-- The stronger one-target squarefree obligation admits the same genuine
exact-head equivalence, using only finite legal combinations. -/
theorem qTarget_mem_squarefreeClosure_iff_bounded_exact_heads
    (p : ℕ) (hp : 1 < p) :
    qTarget p hp ∈ ZetaTwoOptimizerStage.closure ↔
      ∃ B : ℝ, ∀ M : ℕ, ∃ g : QHilbert, g ∈ qSquarefreeCRTSpan ∧
        (∀ n, 0 < n → n ≤ M → qSequence g n = (Nat.log p n : ℝ)) ∧
        ‖g‖ ^ 2 ≤ B := by
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  simpa only [qTarget_sequence] using
    QExactHeadAverages.mem_closure_iff_bounded_target_heads qSquarefreeCRTSpan (qTarget p hp)

/-- Conditional two-prime consumer for finite exact-head data.
The two displayed uniform full-energy budgets are the unresolved arithmetic step. -/
theorem riemannHypothesis_of_bounded_two_finite_exact_heads
    (h2 : ∃ B : ℝ, ∀ M : ℕ, ∃ g : QHilbert, g ∈ finiteWithConstants ∧
      (∀ n, 0 < n → n ≤ M → qSequence g n = (Nat.log 2 n : ℝ)) ∧ ‖g‖ ^ 2 ≤ B)
    (h3 : ∃ B : ℝ, ∀ M : ℕ, ∃ g : QHilbert, g ∈ finiteWithConstants ∧
      (∀ n, 0 < n → n ≤ M → qSequence g n = (Nat.log 3 n : ℝ)) ∧ ‖g‖ ^ 2 ≤ B) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_two_targets_mem_closureWithConstants
    ((qTarget_mem_closureWithConstants_iff_bounded_exact_heads 2 (by norm_num)).mpr h2)
    ((qTarget_mem_closureWithConstants_iff_bounded_exact_heads 3 (by norm_num)).mpr h3)

end RiemannResearch.RH.PrimePowerTarget
