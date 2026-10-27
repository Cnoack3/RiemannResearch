/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QArgumentDoubling
import RiemannResearch.RH.QSquarefreeDilationObstruction
import RiemannResearch.RH.QSquarefreeJumpDistance
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Physical doubling fails to preserve the squarefree legal closure

Source: independently derived from the user's doubling request, 27 October
2026, using the existing square-jump separator. This is the physical sampling
f(2n), not floor dilation. The complete error identity retains its remainder.
The obstruction survives addition of constants and so does not refute residual
invariance or RH. It rules out proving the latter by whole-space invariance.
-/

noncomputable section
namespace RiemannResearch.RH.QArgumentDoublingObstruction
open ZetaTwoHilbert ZetaTwoProbability QArgumentDoubling
open QSquarefreeJumpDistance SquarefreeRadicalDifference PrimePowerTarget

/-- The doubled legal atom has a nonzero four-coordinate defect. -/
theorem doubling_three_squareJump :
    squareJumpFunctional 2 (doubling (qResidue 3)) = 1 := by
  rw [squareJumpFunctional_apply 2 (by decide)]
  simp only [qDifference, doubling_sequence, qSequence_qResidue]
  norm_num [ArithmeticCumulative.residueFraction]

/-- Separation from the enlarged squarefree closure, with the entire remainder. -/
theorem doubling_three_error_energy_exact (F : QHilbert)
    (hF : F ∈ closureWithConstants) :
    ‖doubling (qResidue 3) - F‖ ^ 2 = 1 / (30 * zetaTwo) +
      ‖doubling (qResidue 3) - F - (1 / (30 * zetaTwo)) • squareJumpWitness 2‖ ^ 2 := by
  rw [closureWithConstants_error_energy_exact 2 (by decide) _ F hF,
    doubling_three_squareJump]
  norm_num only [Nat.cast_ofNat]
  rw [show 2 * zetaTwo * 15 = 30 * zetaTwo by ring]

theorem doubling_three_error_sq_lower (F : QHilbert)
    (hF : F ∈ closureWithConstants) :
    1 / (30 * zetaTwo) ≤ ‖doubling (qResidue 3) - F‖ ^ 2 := by
  rw [doubling_three_error_energy_exact F hF]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem doubling_three_not_mem : doubling (qResidue 3) ∉ closureWithConstants := by
  intro hm
  have hz := squareJumpFunctional_zero_on_closureWithConstants 2 (by decide) hm
  rw [doubling_three_squareJump] at hz
  norm_num at hz

private theorem residue_three_mem : qResidue 3 ∈ ZetaTwoOptimizerStage.closure := by
  apply (Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨1, ?_⟩
  norm_num [ZetaTwoOptimizerStage.squarefreeAtom, Nat.prime_three.squarefree]

/-- Whole-space doubling invariance is false, independently of RH. -/
theorem doubling_not_preserve_squarefreeClosure :
    ¬ ∀ f ∈ ZetaTwoOptimizerStage.closure,
      doubling f ∈ ZetaTwoOptimizerStage.closure := by
  intro h
  exact doubling_three_not_mem
    (closure_le_closureWithConstants (h _ residue_three_mem))

/-- Adding constants does not fix the arithmetic obstruction. -/
theorem doubling_not_preserve_closureWithConstants :
    ¬ ∀ f ∈ closureWithConstants, doubling f ∈ closureWithConstants := by
  intro h
  exact doubling_three_not_mem (h _ (closure_le_closureWithConstants residue_three_mem))

/-- The full legal projection cannot commute with physical doubling. -/
theorem doubling_not_commute_projection :
    ¬ ∀ f, doubling (ZetaTwoOptimizerStage.closure.starProjection f) =
      ZetaTwoOptimizerStage.closure.starProjection (doubling f) := by
  intro h
  have he := h (qResidue 3)
  rw [Submodule.starProjection_eq_self_iff.mpr residue_three_mem] at he
  apply doubling_three_not_mem
  apply closure_le_closureWithConstants
  rw [he]
  exact ZetaTwoOptimizerStage.closure.starProjection_apply_mem _

end RiemannResearch.RH.QArgumentDoublingObstruction
