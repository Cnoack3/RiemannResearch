/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerConstrainedHead
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QExactHeadAverages
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.NumberTheory.Primorial
import RiemannResearch.RH.PrimePowerTargetMellin
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# The precise bounded-energy obligation for logarithmic-head optimizers

Source: user-provided RH/CRT continuation agenda, 20 October 2026, Priority 3.
The optimizer is the actual complete-Q inverse-Gram construction on every
squarefree divisor of its period. This is a conditional research reduction:
the displayed uniform bound as the physical head grows remains Open.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets QSquarefreeAffineHead
open RiemannResearch.Analysis

/-- A uniform complete-norm bound for the actual growing-head minimizers places
F₂ in the closed squarefree span. The budget is the only analytic hypothesis. -/
theorem qTarget_mem_of_bounded_logarithmicHeadOptimizer
    (y r : ℕ → ℕ) (hy : ∀ N, N + 2 ≤ y N)
    (hdvd : ∀ N, primorial (N + 2) ∣ primorial (y N))
    (hgap : ∀ N, finitePrimeProduct (N + 2) ≠ finitePrimeProduct (y N))
    (hr : ∀ N, r N ∈ conductors (primorial (y N)))
    (hlarge : ∀ N, N + 2 < r N)
    (B : ℝ)
    (hbudget : ∀ N, ‖logarithmicHeadOptimizer (N + 2) (y N) (r N) (hr N)‖ ^ 2 ≤ B) :
    PrimePowerTarget.qTarget 2 (by norm_num) ∈ qSquarefreeCRTSpan.topologicalClosure := by
  let F : ℕ → QHilbert := fun N => logarithmicHeadOptimizer (N + 2) (y N) (r N) (hr N)
  have hfeasible (N : ℕ) := logarithmicHeadOptimizer_feasible (N + 2) (y N) (r N)
    (by omega) (hy N) (hdvd N) (hgap N) (hr N) (hlarge N)
  have hlegal : ∀ N, F N ∈ qSquarefreeCRTSpan := by
    intro N
    exact divisorStage_le_squarefreeSpan (primorial (y N)) (primorial_pos (y N))
      (squarefree_primorial (y N)) (hfeasible N).1
  apply QExactHeadAverages.mem_closure_of_bounded_target_heads
    qSquarefreeCRTSpan (PrimePowerTarget.qTarget 2 (by norm_num)) F hlegal B hbudget
  intro N n hn hnN
  have hseq := congrFun (PrimePowerTarget.qTarget_sequence 2 (by norm_num)) n
  exact ((hfeasible N).2 n hn (by omega)).trans hseq.symm

/-- Conditional RH consumer for the actual logarithmic-head finite optimizers.
Open: a uniform complete-Q bound on the displayed growing-head family. -/
theorem riemannHypothesis_of_bounded_logarithmicHeadOptimizer
    (y r : ℕ → ℕ) (hy : ∀ N, N + 2 ≤ y N)
    (hdvd : ∀ N, primorial (N + 2) ∣ primorial (y N))
    (hgap : ∀ N, finitePrimeProduct (N + 2) ≠ finitePrimeProduct (y N))
    (hr : ∀ N, r N ∈ conductors (primorial (y N)))
    (hlarge : ∀ N, N + 2 < r N)
    (B : ℝ)
    (hbudget : ∀ N, ‖logarithmicHeadOptimizer (N + 2) (y N) (r N) (hr N)‖ ^ 2 ≤ B) :
    RiemannHypothesis := by
  apply PrimePowerTarget.riemannHypothesis_of_qTarget_mem 2 (by norm_num)
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact qTarget_mem_of_bounded_logarithmicHeadOptimizer y r hy hdvd hgap hr hlarge B hbudget

/-- The finite stage and denominator conditions are always attainable. -/
theorem exists_logarithmicHead_cutoff (x : ℕ) :
    ∃ y : ℕ, max (x + 1) 3 ≤ y ∧ finitePrimeProduct y < finitePrimeProduct x := by
  obtain ⟨y, hgap, hy⟩ :=
    ((eventually_twoStage_gap x).and (eventually_ge_atTop (max (x + 1) 3))).exists
  exact ⟨y, hy, hgap⟩

/-- The least feasible cutoff. Its existence uses the proved Euler-product decay. -/
def selectedLogarithmicCutoff (x : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_logarithmicHead_cutoff x)

theorem selectedLogarithmicCutoff_spec (x : ℕ) :
    max (x + 1) 3 ≤ selectedLogarithmicCutoff x ∧
      finitePrimeProduct (selectedLogarithmicCutoff x) < finitePrimeProduct x := by
  classical
  exact Nat.find_spec (exists_logarithmicHead_cutoff x)

theorem selectedLogarithmicCutoff_gt (x : ℕ) : x < selectedLogarithmicCutoff x := by
  have h := (selectedLogarithmicCutoff_spec x).1
  have hm := le_max_left (x + 1) 3
  omega

theorem selectedLogarithmicCutoff_divides (x : ℕ) :
    primorial x ∣ primorial (selectedLogarithmicCutoff x) :=
  primorial_dvd_primorial (selectedLogarithmicCutoff_gt x).le

/-- The full period itself is a legal anchor beyond the physical head. -/
theorem selectedLogarithmicAnchor_gt (x : ℕ) :
    x < primorial (selectedLogarithmicCutoff x) :=
  (selectedLogarithmicCutoff_gt x).trans_le le_primorial_self

theorem selectedLogarithmicAnchor_mem (x : ℕ) :
    primorial (selectedLogarithmicCutoff x) ∈
      conductors (primorial (selectedLogarithmicCutoff x)) := by
  have hy : 3 ≤ selectedLogarithmicCutoff x :=
    (le_max_right (x + 1) 3).trans (selectedLogarithmicCutoff_spec x).1
  have hL : 1 < primorial (selectedLogarithmicCutoff x) :=
    lt_of_lt_of_le (by omega : 1 < selectedLogarithmicCutoff x) le_primorial_self
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, primorial_ne_zero _⟩, hL⟩

/-- One entirely specified actual optimizer for each increasing head length.
No finite-stage feasibility data remain as theorem hypotheses. -/
def selectedLogarithmicHeadOptimizer (N : ℕ) : QHilbert :=
  logarithmicHeadOptimizer (N + 2) (selectedLogarithmicCutoff (N + 2))
    (primorial (selectedLogarithmicCutoff (N + 2))) (selectedLogarithmicAnchor_mem (N + 2))

theorem selectedLogarithmicHeadOptimizer_feasible (N : ℕ) :
    selectedLogarithmicHeadOptimizer N ∈ qSquarefreeCRTSpan ∧
      ∀ n, 0 < n → n ≤ N + 2 →
        qSequence (selectedLogarithmicHeadOptimizer N) n = (Nat.log 2 n : ℝ) := by
  have hf := logarithmicHeadOptimizer_feasible (N + 2)
    (selectedLogarithmicCutoff (N + 2)) (primorial (selectedLogarithmicCutoff (N + 2)))
    (by omega) (selectedLogarithmicCutoff_gt (N + 2)).le
    (selectedLogarithmicCutoff_divides (N + 2))
    (ne_of_gt (selectedLogarithmicCutoff_spec (N + 2)).2)
    (selectedLogarithmicAnchor_mem (N + 2)) (selectedLogarithmicAnchor_gt (N + 2))
  exact ⟨divisorStage_le_squarefreeSpan _ (primorial_pos _) (squarefree_primorial _) hf.1, hf.2⟩

/-- Conditional membership with the only remaining hypothesis the actual energy budget.
The selected cutoff is feasible; no optimality across different periods is asserted. -/
theorem qTarget_mem_of_bounded_selectedLogarithmicHeadOptimizer
    (B : ℝ) (hbudget : ∀ N, ‖selectedLogarithmicHeadOptimizer N‖ ^ 2 ≤ B) :
    PrimePowerTarget.qTarget 2 (by norm_num) ∈ qSquarefreeCRTSpan.topologicalClosure := by
  apply QExactHeadAverages.mem_closure_of_bounded_target_heads qSquarefreeCRTSpan
    (PrimePowerTarget.qTarget 2 (by norm_num)) selectedLogarithmicHeadOptimizer
    (fun N => (selectedLogarithmicHeadOptimizer_feasible N).1) B hbudget
  intro N n hn hnN
  exact ((selectedLogarithmicHeadOptimizer_feasible N).2 n hn (by omega)).trans
    (congrFun (PrimePowerTarget.qTarget_sequence 2 (by norm_num)) n).symm

/-- Conditional RH consumer; uniform complete-Q control of this actual family remains Open. -/
theorem riemannHypothesis_of_bounded_selectedLogarithmicHeadOptimizer
    (B : ℝ) (hbudget : ∀ N, ‖selectedLogarithmicHeadOptimizer N‖ ^ 2 ≤ B) :
    RiemannHypothesis := by
  apply PrimePowerTarget.riemannHypothesis_of_qTarget_mem 2 (by norm_num)
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact qTarget_mem_of_bounded_selectedLogarithmicHeadOptimizer B hbudget


end RiemannResearch.RH.QPrimePowerSieve
