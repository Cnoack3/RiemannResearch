/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeHeadLeakage
import RiemannResearch.RH.QSquarefreeSchurRepresentation
import RiemannResearch.RH.QSquarefreeSchurCoercivity
import RiemannResearch.RH.QDivisorHeadCoercivity
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.FiniteHilbertGramMatrix

/-!
# Complete Schur representation of physical head leakage
Source: SquarefreePrefixCovarianceResearch20261101.md, using the existing
complete-squarefree Schur projection theorem. No arithmetic decay is asserted.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeHeadLeakage
open ZetaTwoHilbert QFiniteSupportDualCriterion
open QSquarefreeSchurRepresentation QSquarefreeSchurCoercivity QDivisorHeadCoercivity
open RiemannResearch.Analysis.FiniteHilbertGram

/-- Every high conductor survives through the full screened Schur Gram. -/
theorem leakage_eq_schur_tail (N H d0 : ℕ) (hH : 1 ≤ H)
    (hanchor : H < d0) (hd0N : d0 ≤ N + 1) (hsf : Squarefree d0)
    (z : QHilbert) :
    leakage N H z =
      let p := Fintype.linearCombination ℝ (squarefreeSchurFamily N H d0)
        ((gramMatrix (squarefreeSchurFamily N H d0))⁻¹.mulVec
          (cross (squarefreeHeadFamily H d0) (finiteHead H z)))
      p - finiteHead H p := by
  simp only [leakage, projectedHead,
    stageProjection_finiteHead_eq_schur_inverseGram N H d0 hH hanchor hd0N hsf]

end RiemannResearch.RH.QSquarefreeHeadLeakage
