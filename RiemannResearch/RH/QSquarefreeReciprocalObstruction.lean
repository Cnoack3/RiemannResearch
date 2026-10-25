/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeBoundary
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Tactic.NormNum

/-!
# Shifted reciprocal multiplication does not preserve squarefree legality

Source: the user's measure-change agenda and the existing checked four-site
functional. Its value on B g_2 is exactly 1/8, so a general multiplier-invariance
argument cannot be used to discharge the regularity criteria.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeReciprocalObstruction
open ZetaTwoHilbert QSquarefreeBoundary QShiftedReciprocal

/-- Reciprocal smoothing violates the four-site identity already on g₂. -/
theorem fourSiteFunctional_B_qResidue_two :
    fourSiteFunctional (B (qResidue 2)) = (1 : ℝ) / 8 := by
  rw [fourSiteFunctional_apply]
  simp only [qSequence_B, qSequence_qResidue]
  norm_num [ArithmeticCumulative.residueFraction]

/-- The physical shifted reciprocal does not preserve the squarefree legal span. -/
theorem B_qResidue_two_not_mem :
    B (qResidue 2) ∉ ZetaTwoOptimizerStage.closure := by
  intro h
  have hz := fourSiteFunctional_zero_on_closure h
  rw [fourSiteFunctional_B_qResidue_two] at hz
  norm_num at hz

theorem B_not_preserves_closure :
    ¬ (∀ f ∈ ZetaTwoOptimizerStage.closure,
      B f ∈ ZetaTwoOptimizerStage.closure) := by
  intro h
  exact B_qResidue_two_not_mem (h (qResidue 2) qResidue_two_mem)

end RiemannResearch.RH.QSquarefreeReciprocalObstruction
