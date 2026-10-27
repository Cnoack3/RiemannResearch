/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QBoundedSubspaceEvaluation
import RiemannResearch.RH.QConductorEstimates
import RiemannResearch.Analysis.ConductorLogEnvelope
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.Analysis.ExhaustiveProjectionWalk

/-!
# High-conductor projection bounds in a fixed bounded Q subspace

Source: `SingleConductorProjectionBound.md`. The uniform-evaluation constant
of the fixed subspace controls residue projection in norm and pointwise.
No bound uniform over the canonical stage number is assumed or concluded.
-/

noncomputable section
namespace RiemannResearch.RH.QBoundedResidueProjection
open ZetaTwoHilbert ZetaTwoProbability QBoundedSubspaceEvaluation

theorem qResidue_qL1_eq_mean (d : ℕ) :
    qL1 (qResidue d) = inner ℝ qOne (qResidue d) := by
  unfold qL1
  rw [qOne_inner_weighted]
  apply tsum_congr
  intro n
  rw [abs_of_nonneg (qResidue_physical_nonneg d n)]

theorem qResidue_projection_norm_le_log_div
    (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u : QHilbert, u ∈ U →
      ∀ n : ℕ, |qSequence u n| ≤ C * ‖u‖)
    (d : ℕ) (hd : 2 ≤ d) :
    ‖U.starProjection (qResidue d)‖ ≤
      C * ((2 + Real.log (d : ℝ)) / (zetaTwo * d)) := by
  have h := projection_norm_le_qL1 U C hC hbound (qResidue d)
  rw [qResidue_qL1_eq_mean] at h
  exact h.trans (mul_le_mul_of_nonneg_left (qResidue_mean_le_log_div d hd) hC)

theorem qResidue_projection_physical_le_log_div
    (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u : QHilbert, u ∈ U →
      ∀ n : ℕ, |qSequence u n| ≤ C * ‖u‖)
    (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    |qSequence (U.starProjection (qResidue d)) n| ≤
      C ^ 2 * ((2 + Real.log (d : ℝ)) / (zetaTwo * d)) := by
  have h := projection_physical_le_qL1 U C hC hbound (qResidue d) n
  rw [qResidue_qL1_eq_mean] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (qResidue_mean_le_log_div d hd) (sq_nonneg C))

/-- Every vector in an actual finite squarefree stage has a bounded
physical sequence. The bound can depend on the vector and on the stage. -/
theorem stage_physical_bounded (N : ℕ) (u : QHilbert)
    (hu : u ∈ ZetaTwoOptimizerStage.stage N) :
    ∃ C : ℝ, ∀ n : ℕ, |qSequence u n| ≤ C := by
  unfold ZetaTwoOptimizerStage.stage
    RiemannResearch.Analysis.ExhaustiveWalk.walkSpan at hu
  induction hu using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      refine ⟨1, ?_⟩
      intro n
      change |qSequence (ZetaTwoOptimizerStage.squarefreeAtom i.val) n| ≤ 1
      by_cases hs : Squarefree (i.val + 2)
      · rw [ZetaTwoOptimizerStage.squarefreeAtom, if_pos hs]
        exact qResidue_physical_abs_le_one _ n
      · rw [ZetaTwoOptimizerStage.squarefreeAtom, if_neg hs]
        change |qSequenceLinear 0 n| ≤ 1
        rw [map_zero]
        norm_num
  | zero =>
      refine ⟨0, ?_⟩
      intro n
      change |qSequenceLinear 0 n| ≤ 0
      rw [map_zero]
      simp
  | add v w hv hw ihv ihw =>
      obtain ⟨C, hC⟩ := ihv
      obtain ⟨D, hD⟩ := ihw
      refine ⟨C + D, ?_⟩
      intro n
      change |qSequenceLinear (v + w) n| ≤ C + D
      rw [map_add]
      change |qSequence v n + qSequence w n| ≤ C + D
      exact (abs_add_le _ _).trans (add_le_add (hC n) (hD n))
  | smul c v hv ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨|c| * C, ?_⟩
      intro n
      change |qSequenceLinear (c • v) n| ≤ |c| * C
      rw [map_smul]
      change |c * qSequence v n| ≤ |c| * C
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hC n) (abs_nonneg c)

/-- A fixed canonical stage has an evaluation constant; no uniformity in N. -/
theorem exists_stage_uniform_physical_bound (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : QHilbert, u ∈ ZetaTwoOptimizerStage.stage N →
      ∀ n : ℕ, |qSequence u n| ≤ C * ‖u‖ :=
  exists_uniform_physical_bound (ZetaTwoOptimizerStage.stage N)
    (stage_physical_bounded N)

end RiemannResearch.RH.QBoundedResidueProjection

namespace RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.Analysis.ConductorLogEnvelope

/-- A conductor logarithm is converted to the physical-site logarithm
using both elementary residue bounds. -/
theorem log_mul_qResidue_le_physical_log (d n : ℕ) (hd : 2 ≤ d) (hn : 0 < n) :
    (2 + Real.log (d : ℝ)) * qSequence (qResidue d) n ≤
      2 + Real.log (n : ℝ) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : 0 ≤ 2 + Real.log (d : ℝ) := by linarith [Real.log_nonneg hd1]
  by_cases hdn : d ≤ n
  · have hlog : Real.log (d : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hdn)
    have hres : qSequence (qResidue d) n ≤ 1 :=
      (le_abs_self _).trans (qResidue_physical_abs_le_one d n)
    calc
      _ ≤ (2 + Real.log (d : ℝ)) * 1 := mul_le_mul_of_nonneg_left hres hbase
      _ ≤ _ := by linarith
  · have hnd : (n : ℝ) ≤ d := by exact_mod_cast (show n ≤ d by omega)
    exact (mul_le_mul_of_nonneg_left (qResidue_physical_le_div d n) hbase).trans
      (two_add_log_mul_ratio_le (d : ℝ) (n : ℝ) hn1 hnd)

end RiemannResearch.RH.ZetaTwoHilbert
