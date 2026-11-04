/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QSquarefreeJumpDistance
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Full and squarefree residue projections

Source: user's basis-comparison research request, 4 November 2026. The nested
projection energy is a Hilbert-space identity; the four-site square-jump
witness is reused from QSquarefreeJumpDistance. The gap identity retains the
complete norm-square correction. The g_4 obstruction is unconditional and
does not assert a positive gap for the particular target 1.
-/

noncomputable section
open scoped BigOperators
open RiemannResearch.RH
open ZetaTwoHilbert
open RiemannResearch.Analysis.ExhaustiveWalk

namespace RiemannResearch.RH.QResidueBasisComparison

theorem squarefree_stage_le_full_stage (n : ℕ) :
    ZetaTwoOptimizerStage.stage n ≤ QFullResidueProjection.stage n := by
  unfold ZetaTwoOptimizerStage.stage QFullResidueProjection.stage walkSpan
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  by_cases hs : Squarefree ((i : ℕ) + 2)
  · simp only [ZetaTwoOptimizerStage.squarefreeAtom, id_eq, if_pos hs]
    exact Submodule.subset_span ⟨i, rfl⟩
  · simp [ZetaTwoOptimizerStage.squarefreeAtom, hs]

theorem squarefree_full_error_gap (n : ℕ) :
    ZetaTwoOptimizerStage.error n =
      ‖qOne - QFullResidueProjection.candidate n‖ ^ 2 +
      ‖QFullResidueProjection.candidate n - ZetaTwoOptimizerStage.optimizer n‖ ^ 2 := by
  have h := nested_projection_energy (ZetaTwoOptimizerStage.stage n)
    (QFullResidueProjection.stage n) (squarefree_stage_le_full_stage n) qOne
  simpa only [ZetaTwoOptimizerStage.error, ZetaTwoOptimizerStage.residual,
    ZetaTwoOptimizerStage.optimizer, QFullResidueProjection.candidate_eq_projection] using h

theorem residue_four_jump :
    QSquarefreeJumpDistance.squareJumpFunctional 2 (qResidue 4) = -1 := by
  rw [QSquarefreeJumpDistance.squareJumpFunctional_apply 2 (by decide)]
  simp only [SquarefreeRadicalDifference.qDifference, qSequence_qResidue]
  norm_num [ArithmeticCumulative.residueFraction]

theorem residue_four_separation (F : QHilbert)
    (hF : F ∈ ZetaTwoProbability.qSquarefreeCRTSpan.topologicalClosure) :
    1 / (30 * ZetaTwoProbability.zetaTwo) ≤ ‖qResidue 4 - F‖ ^ 2 := by
  have h := QSquarefreeJumpDistance.squarefree_error_sq_lower_bound 2 (by decide)
    (qResidue 4) F hF
  rw [residue_four_jump] at h
  norm_num at h ⊢
  convert h using 1
  ring

end RiemannResearch.RH.QResidueBasisComparison
