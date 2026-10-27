/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QExponentialMoment
import RiemannResearch.RH.QSquarefreeExponentialMoment
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.CRTCarryArithmetic
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Push
import Mathlib.Order.Filter.Defs

/-!
# Finite-stage exponential moments and the surviving-residual obstruction

Source: independently derived continuation of the user's prime-resampling
agenda. Each actual finite-stage correction is physically bounded and has
every exponential moment. If the actual limiting residual is nonzero, all
positive exponential moments of the moving corrections tend to infinity.
Individual finite-stage finiteness therefore cannot supply the common budget
in the limiting criterion.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.ZetaTwoOptimizerStage
open ZetaTwoHilbert
open RiemannResearch.Analysis.ExhaustiveWalk

/-- Every individual finite legal stage has bounded physical coordinates.
The bound may depend on the stage and the vector; no uniform assertion is made. -/
theorem stage_physical_bounded (N : ℕ) (u : QHilbert) (hu : u ∈ stage N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |qSequence u n| ≤ C := by
  have hq : qSequence (0 : QHilbert) = 0 := qSequenceLinear.map_zero
  unfold stage walkSpan at hu
  induction hu using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      change ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        |qSequence (squarefreeAtom i.val) n| ≤ C
      by_cases hs : Squarefree (i.val + 2)
      · refine ⟨1, zero_le_one, ?_⟩
        intro n
        rw [squarefreeAtom, if_pos hs, qSequence_qResidue]
        exact CRTCarryArithmetic.residueFraction_abs_le_one (i.val + 2) n
      · refine ⟨0, le_rfl, ?_⟩
        intro n
        rw [squarefreeAtom, if_neg hs]
        simp only [hq, Pi.zero_apply, abs_zero, le_refl]
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      intro n
      simp only [hq, Pi.zero_apply, abs_zero, le_refl]
  | add x y hx hy ihx ihy =>
      obtain ⟨Cx, hCx, hxbound⟩ := ihx
      obtain ⟨Cy, hCy, hybound⟩ := ihy
      refine ⟨Cx + Cy, add_nonneg hCx hCy, ?_⟩
      intro n
      change |qSequenceLinear (x + y) n| ≤ Cx + Cy
      rw [map_add]
      change |qSequence x n + qSequence y n| ≤ Cx + Cy
      exact (abs_add_le _ _).trans (add_le_add (hxbound n) (hybound n))
  | smul c x hx ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      refine ⟨|c| * C, mul_nonneg (abs_nonneg c) hC, ?_⟩
      intro n
      change |qSequenceLinear (c • x) n| ≤ |c| * C
      rw [map_smul]
      change |c * qSequence x n| ≤ |c| * C
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbound n) (abs_nonneg c)

end RiemannResearch.RH.ZetaTwoOptimizerStage

namespace RiemannResearch.RH.QExponentialMoment
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeSmoothedProjection

theorem stage_exponentialMoment_summable
    (N : ℕ) (u : QHilbert) (hu : u ∈ stage N) (κ : ℝ) :
    Summable (fun n : ℕ =>
      positiveQWeight n * Real.exp (κ * |qSequence u n|)) := by
  obtain ⟨C, _, hbound⟩ := stage_physical_bounded N u hu
  exact exponentialMoment_summable_of_physical_bound u C hbound κ

/-- Each actual canonical correction has every exponential moment. This is
individual finiteness and does not provide a common moment budget as N grows. -/
theorem movingCorrection_exponentialMoment_summable (N : ℕ) (κ : ℝ) :
    Summable (fun n : ℕ =>
      positiveQWeight n * Real.exp (κ * |qSequence (movingCorrection N) n|)) := by
  apply stage_exponentialMoment_summable N (movingCorrection N)
  exact (stage N).starProjection_apply_mem _

theorem finiteCorrection_exponentialMoment_summable (N : ℕ) (κ : ℝ) :
    Summable (fun n : ℕ =>
      positiveQWeight n * Real.exp (κ * |qSequence (finiteCorrection N) n|)) := by
  apply stage_exponentialMoment_summable N (finiteCorrection N)
  exact (stage N).starProjection_apply_mem _

end RiemannResearch.RH.QExponentialMoment

namespace RiemannResearch.RH.QSquarefreeExponentialMoment
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeSmoothedProjection
open QExponentialMoment

/-- If the actual residual survives, every positive exponential moment of
its bounded finite-stage corrections tends to infinity. -/
theorem moving_exponentialMoment_tendsto_atTop_of_residual_ne_zero
    (κ : ℝ) (hκ : 0 < κ) (hr : limitingResidual ≠ 0) :
    Tendsto (fun N => ∑' n : ℕ, positiveQWeight n *
      Real.exp (κ * |qSequence (movingCorrection N) n|)) atTop atTop := by
  have hn : ¬ Summable (fun n : ℕ =>
      positiveQWeight n * Real.exp (κ * |qSequence correction n|)) := by
    intro hs
    exact hr (residual_zero_of_correction_exponentialMoment_summable κ hκ hs)
  apply tendsto_atTop.2
  intro M
  have hex : ∃ S : Finset ℕ, M < ∑ n ∈ S,
      positiveQWeight n * Real.exp (κ * |qSequence correction n|) := by
    by_contra h
    push Not at h
    apply hn
    exact summable_of_sum_le
      (fun n => mul_nonneg (positiveQWeight_nonneg n) (Real.exp_pos _).le) h
  obtain ⟨S, hS⟩ := hex
  have he := (movingExponentialFiniteSum_tendsto κ S).eventually (Ioi_mem_nhds hS)
  filter_upwards [he] with N hN
  exact le_of_lt (hN.trans_le ((movingCorrection_exponentialMoment_summable N κ).sum_le_tsum S
    (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (Real.exp_pos _).le)))
end RiemannResearch.RH.QSquarefreeExponentialMoment
