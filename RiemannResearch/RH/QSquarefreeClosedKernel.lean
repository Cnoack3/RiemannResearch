/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeCorrectionKernel
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.ResidualizedProjectionKernel

/-!
# Kernel of the closed squarefree projection

The Riesz representation of evaluation gives an exact full-tail formula for
the Q-orthogonal projection. This is a signed kernel, not a conditional
averaging kernel. Source: the Hilbert projection theorem as implemented in
Mathlib.Analysis.InnerProductSpace.Projection.Submodule and the existing
finite-stage QSquarefreeCorrectionKernel. No regularity bound is assumed.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeClosedKernel
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeCorrectionKernel

def closedKernel (n : ℕ) : QHilbert := closure.starProjection (evaluation n)

theorem projected_physical_pairing (f : QHilbert) (n : ℕ) :
    qSequence (closure.starProjection f) n = inner ℝ f (closedKernel n) := by
  rw [← inner_evaluation]
  exact RiemannResearch.Analysis.ResidualizedProjectionKernel.projection_inner
    closure f (evaluation n)

theorem projected_physical_tsum (f : QHilbert) (n : ℕ) :
    qSequence (closure.starProjection f) n =
      ∑' m, positiveQWeight m * qSequence f m * qSequence (closedKernel n) m := by
  rw [projected_physical_pairing, qInner_weighted]


end RiemannResearch.RH.QSquarefreeClosedKernel
