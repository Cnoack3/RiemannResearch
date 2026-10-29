/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueEnergyCertificates
import RiemannResearch.RH.QCRTMinimumEnergy
import RiemannResearch.RH.QSquarefreeExactHeadAverages
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QCRTCoprimeApproximation
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse

/-!
# Exact period gains and head costs on actual primorial schedules

Source: user-provided RH_Exact_Head_Energy_Proof_Handoff_2026-10-28.md,
Section 9.A, for the signed recurrence and its intended RH application.
All minima use the complete Q inner product. The two-stage bridge fixes
the old head at the new period, and every distance-square is retained.

The identities and finite schedule properties are unconditional.
The RH declaration is a conditional research reduction: its cumulative
signed-budget hypothesis remains an open arithmetic obligation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTPeriodHeadBalance
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets QResidueHeadSpace
open QResidueEnergyCertificates QSquarefreeAffineHead QCRTCoprimeApproximation
open QCRTMinimumEnergy

def minimumAt (j H : ℕ) : QHilbert :=
  exactHeadAdjustment (conductors (primorial (j + 2))) H (approximant j)

theorem minimumAt_mem (j H : ℕ) :
    minimumAt j H ∈ divisorStage (primorial (j + 2)) := by
  rw [divisorStage_eq_dictionary _ (primorial_pos _)]
  exact (exactHeadAdjustment_same_head _ _ _ (seed_mem_dictionary j)).1

theorem minimumAt_head (j H : ℕ) (hH : H ≤ j + 1) (n : ℕ)
    (hn : 0 < n) (hnH : n ≤ H) : qSequence (minimumAt j H) n = 1 := by
  exact ((exactHeadAdjustment_same_head _ _ _ (seed_mem_dictionary j)).2 n hn hnH).trans
    (approximant_exact_head j n hn (hnH.trans hH))

theorem minimumAt_completion (j H : ℕ) (hH : H ≤ j + 1)
    (f : QHilbert) (hf : f ∈ divisorStage (primorial (j + 2)))
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = 1) :
    ‖f‖ ^ 2 = ‖minimumAt j H‖ ^ 2 + ‖f - minimumAt j H‖ ^ 2 := by
  apply exactHeadAdjustment_completion _ _ _ _ (seed_mem_dictionary j)
  · rwa [← divisorStage_eq_dictionary _ (primorial_pos _)]
  · intro n hn hnH
    rw [hh n hn hnH, approximant_exact_head j n hn (hnH.trans hH)]

theorem minimumAt_period_gain (i j H : ℕ) (hij : i ≤ j) (hH : H ≤ i + 1) :
    ‖minimumAt i H‖ ^ 2 = ‖minimumAt j H‖ ^ 2 +
      ‖minimumAt i H - minimumAt j H‖ ^ 2 := by
  apply minimumAt_completion j H (by omega)
  · exact divisorStage_mono
      (primorial_dvd_primorial (Nat.add_le_add_right hij 2)) (minimumAt_mem i H)
  · exact minimumAt_head i H hH

theorem minimumAt_head_cost (j H K : ℕ) (hHK : H ≤ K) :
    ‖minimumAt j K‖ ^ 2 = ‖minimumAt j H‖ ^ 2 +
      ‖minimumAt j K - minimumAt j H‖ ^ 2 :=
  exactHeadAdjustment_head_gain _ hHK _ (seed_mem_dictionary j)

def periodGain (σ : ℕ → ℕ) (n : ℕ) : ℝ :=
  ‖minimumAt (σ n) (n + 1) - minimumAt (σ (n + 1)) (n + 1)‖ ^ 2

def headCost (σ : ℕ → ℕ) (n : ℕ) : ℝ :=
  ‖minimumAt (σ (n + 1)) (n + 2) - minimumAt (σ (n + 1)) (n + 1)‖ ^ 2

def stageEnergy (σ : ℕ → ℕ) (n : ℕ) : ℝ :=
  ‖minimumAt (σ n) (n + 1)‖ ^ 2

theorem stageEnergy_step (σ : ℕ → ℕ) (hσ : Monotone σ)
    (hhead : ∀ n, n ≤ σ n) (n : ℕ) :
    stageEnergy σ (n + 1) = stageEnergy σ n - periodGain σ n + headCost σ n := by
  have hA := minimumAt_period_gain (σ n) (σ (n + 1)) (n + 1)
    (hσ (Nat.le_succ n)) (Nat.add_le_add_right (hhead n) 1)
  have hB := minimumAt_head_cost (σ (n + 1)) (n + 1) (n + 2) (by omega)
  dsimp [stageEnergy, periodGain, headCost]
  simpa only [Nat.add_assoc] using (show
    ‖minimumAt (σ (n + 1)) (n + 2)‖ ^ 2 =
      ‖minimumAt (σ n) (n + 1)‖ ^ 2 -
      ‖minimumAt (σ n) (n + 1) - minimumAt (σ (n + 1)) (n + 1)‖ ^ 2 +
      ‖minimumAt (σ (n + 1)) (n + 2) - minimumAt (σ (n + 1)) (n + 1)‖ ^ 2 by linarith)

theorem stageEnergy_telescope (σ : ℕ → ℕ) (hσ : Monotone σ)
    (hhead : ∀ n, n ≤ σ n) (N : ℕ) :
    stageEnergy σ N = stageEnergy σ 0 +
      ∑ n ∈ Finset.range N, (headCost σ n - periodGain σ n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [stageEnergy_step σ hσ hhead, ih, Finset.sum_range_succ]
    ring


theorem minimumAt_legal (j H : ℕ) : minimumAt j H ∈ qSquarefreeCRTSpan :=
  divisorStage_le_squarefreeSpan _ (primorial_pos _) (squarefree_primorial _)
    (minimumAt_mem j H)

/-- Exact equivalence of the proposed signed budget and the full energy bound. -/
theorem budget_bound_iff (σ : ℕ → ℕ) (hσ : Monotone σ)
    (hhead : ∀ n, n ≤ σ n) (C : ℝ) :
    (∀ N, (∑ n ∈ Finset.range N, (headCost σ n - periodGain σ n)) ≤
      C - stageEnergy σ 0) ↔ ∀ N, stageEnergy σ N ≤ C := by
  constructor
  · intro hb N
    rw [stageEnergy_telescope σ hσ hhead N]
    linarith [hb N]
  · intro hb N
    have he := stageEnergy_telescope σ hσ hhead N
    linarith [hb N]

/-- Conditional research reduction: the signed cumulative budget remains the
unproved arithmetic input. All legality, head, and norm-conversion providers
are discharged here for the actual slower-head primorial schedule. -/
theorem riemannHypothesis_of_balance_bound (σ : ℕ → ℕ) (hσ : Monotone σ)
    (hhead : ∀ n, n ≤ σ n) (C : ℝ)
    (hbudget : ∀ N, (∑ n ∈ Finset.range N, (headCost σ n - periodGain σ n)) ≤
      C - stageEnergy σ 0) : RiemannHypothesis := by
  let F : ℕ → QHilbert := fun N => minimumAt (σ N) (N + 1)
  have hb := (budget_bound_iff σ hσ hhead C).mp hbudget
  have hbound : ∀ N, ‖qOne - F N‖ ^ 2 ≤ 2 + 2 * C := by
    intro N
    have hn := norm_sub_le qOne (F N)
    rw [qOne_norm] at hn
    have he : ‖F N‖ ^ 2 ≤ C := hb N
    nlinarith [norm_nonneg (qOne - F N), norm_nonneg (F N),
      sq_nonneg (‖F N‖ - 1)]
  exact (QSquarefreeExactHeadAverages.squarefree_closure_capacity_and_rh_of_bounded_exact_heads
    F (fun N => minimumAt_legal _ _) hbound
      (fun N n hn hnN => minimumAt_head _ _ (Nat.add_le_add_right (hhead N) 1)
        n hn (by omega))).2.2

end RiemannResearch.RH.QCRTPeriodHeadBalance
