/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeClosedKernel
import RiemannResearch.RH.QSquarefreeCorrectionKernel
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import RiemannResearch.RH.QSquarefreeResidualTail
import Mathlib.Tactic.Push

/-!
# Column bounds for the squarefree projected evaluation kernel

The mean of the complementary evaluation kernel is the corresponding coordinate
of the limiting residual. The bounded-annihilator theorem from
`QSquarefreeResidualTail` then converts a bound on a single kernel column
into vanishing of that residual coordinate. Each column may have its own bound.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeKernelColumnRigidity
open ZetaTwoHilbert ZetaTwoOptimizerStage
open QSquarefreeCorrectionKernel QSquarefreeClosedKernel
open QSquarefreeResidualTail

private theorem evaluation_physically_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, |qSequence (evaluation n) k| ≤ C := by
  refine ⟨|qSequence (evaluation n) n|, abs_nonneg _, ?_⟩
  intro k
  by_cases hkn : k = n
  · subst k
    exact le_rfl
  · have hz : qSequence (evaluation n) k = 0 := by
      cases n with
      | zero => cases k <;> simp [evaluation, qSequence]
      | succ n =>
        cases k with
        | zero => simp
        | succ k =>
          have hkn' : k ≠ n := fun h => hkn (congrArg Nat.succ h)
          simp [evaluation, qSequence, lp.single_apply, hkn']
    rw [hz, abs_zero]
    exact abs_nonneg _

/-- The mean of the complementary evaluation kernel is exactly the corresponding
coordinate of the actual residual. No regularity premise is required. -/
theorem kernel_complement_mean (n : ℕ) :
    inner ℝ qOne (evaluation n - closedKernel n) =
      qSequence limitingResidual n := by
  rw [inner_sub_right, inner_evaluation,
    ← projected_physical_pairing qOne n]
  change qSequenceLinear qOne n -
      qSequenceLinear (closure.starProjection qOne) n =
    qSequenceLinear (qOne - closure.starProjection qOne) n
  exact (congrFun (qSequenceLinear.map_sub qOne
    (closure.starProjection qOne)) n).symm

/-- A bound on a single column forces the corresponding residual coordinate to vanish. -/
theorem residual_coordinate_zero_of_closedKernel_bounded
    (n : ℕ) (C : ℝ)
    (hK : ∀ k : ℕ, |qSequence (closedKernel n) k| ≤ C) :
    qSequence limitingResidual n = 0 := by
  obtain ⟨D, hD, hE⟩ := evaluation_physically_bounded n
  have hC : 0 ≤ C := by simpa using hK 0
  let u : QHilbert := evaluation n - closedKernel n
  have hu : u ∈ closureᗮ := by
    exact Submodule.sub_starProjection_mem_orthogonal
      (K := closure) (evaluation n)
  have hb : ∀ k : ℕ, |qSequence u k| ≤ D + C := by
    intro k
    have hs : qSequence u k =
        qSequence (evaluation n) k - qSequence (closedKernel n) k := by
      exact congrFun (qSequenceLinear.map_sub (evaluation n) (closedKernel n)) k
    rw [hs]
    calc
      |qSequence (evaluation n) k - qSequence (closedKernel n) k|
          ≤ |qSequence (evaluation n) k| + |qSequence (closedKernel n) k| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (qSequence (evaluation n) k) (-qSequence (closedKernel n) k)
      _ ≤ D + C := add_le_add (hE k) (hK k)
  have hm := bounded_annihilator_mean_eq_zero u hu
    (D + C) (add_nonneg hD hC) hb
  change inner ℝ qOne (evaluation n - closedKernel n) = 0 at hm
  rwa [kernel_complement_mean] at hm

/-- A separate bound for each column suffices to make the entire residual vanish.
The column bounds remain open. -/
theorem residual_zero_of_each_closedKernel_bounded
    (hK : ∀ n : ℕ, ∃ C : ℝ,
      ∀ k : ℕ, |qSequence (closedKernel n) k| ≤ C) :
    limitingResidual = 0 := by
  apply qSequence_injective
  funext n
  obtain ⟨C, hC⟩ := hK n
  have hn := residual_coordinate_zero_of_closedKernel_bounded n C hC
  rw [hn]
  cases n <;> simp [qSequence]

/-- A nonzero residual coordinate forces the corresponding kernel column to be unbounded. -/
theorem closedKernel_unbounded_of_residual_coordinate_ne_zero
    (n : ℕ) (hn : qSequence limitingResidual n ≠ 0) (C : ℝ) :
    ∃ k : ℕ, C < |qSequence (closedKernel n) k| := by
  by_contra h
  push Not at h
  exact hn (residual_coordinate_zero_of_closedKernel_bounded n C h)

end RiemannResearch.RH.QSquarefreeKernelColumnRigidity
