/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QEvenClosure
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.QSquarefreeJumpDistance
import RiemannResearch.RH.PrimePowerTwoTargetCriterion
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.QParityConditionalTarget
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Quantitative failure of squarefree floor-dilation invariance

Source: user-provided two-prime Mellin/parity handoff, 20 October 2026,
Section 6.4. The existing continuous floor dilation preserves the full
all-conductor legal closure. It does not preserve the squarefree closure,
even after real constants are added. The complete error identity retains
the entire orthogonal remainder. This is a method obstruction, not a
nonmembership claim about the logarithmic target F₂.
-/

noncomputable section
open scoped RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParitySignal
open QFloorDilation QSquarefreeJumpDistance SquarefreeRadicalDifference

theorem closure_le_closureWithConstants :
    ZetaTwoOptimizerStage.closure ≤ closureWithConstants :=
  le_sup_left.trans
    (ZetaTwoOptimizerStage.closure ⊔ Submodule.span ℝ {qOne}).le_topologicalClosure

theorem qOne_mem_closureWithConstants : qOne ∈ closureWithConstants := by
  apply (ZetaTwoOptimizerStage.closure ⊔ Submodule.span ℝ {qOne}).le_topologicalClosure
  exact (show Submodule.span ℝ {qOne} ≤
    ZetaTwoOptimizerStage.closure ⊔ Submodule.span ℝ {qOne} from le_sup_right)
    (Submodule.subset_span (by simp))

theorem qEven_mem_closureWithConstants : qEven ∈ closureWithConstants := by
  apply (QEvenClosure.qEven_mem_iff closureWithConstants
    (closure_le_closureWithConstants QParityConditionalTarget.qResidue_two_mem_closure)).2
  exact qOne_mem_closureWithConstants

/-- The four-site test continues to vanish when real constants are allowed. -/
theorem squareJumpFunctional_zero_on_closureWithConstants
    (a : ℕ) (ha : 2 ≤ a) {f : QHilbert} (hf : f ∈ closureWithConstants) :
    squareJumpFunctional a f = 0 := by
  let L := squareJumpFunctional a
  have hH : ZetaTwoOptimizerStage.closure ≤ L.ker := by
    change (Submodule.span ℝ
      (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).topologicalClosure ≤ L.ker
    apply (Submodule.span ℝ
      (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).topologicalClosure_minimal
      ?_ L.isClosed_ker
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    unfold ZetaTwoOptimizerStage.squarefreeAtom
    split_ifs with hi
    · exact squareJumpWitness_inner_eq_zero a ha _
        (qSquarefreeCRTSpan.le_topologicalClosure
          (Submodule.subset_span ⟨⟨i + 2, by omega, hi⟩, rfl⟩))
    · exact L.ker.zero_mem
  have hOne : qOne ∈ L.ker := by
    change squareJumpFunctional a qOne = 0
    rw [squareJumpFunctional_apply a ha,
      qDifference_qOne (a ^ 2) (by nlinarith), qDifference_qOne a ha, sub_self]
  exact ((ZetaTwoOptimizerStage.closure ⊔ Submodule.span ℝ {qOne}).topologicalClosure_minimal
    (sup_le hH ((Submodule.span_singleton_le_iff_mem qOne L.ker).2 hOne))
    L.isClosed_ker) hf

/-- Exact energy decomposition against the enlarged closure, with signed defect. -/
theorem closureWithConstants_error_energy_exact (a : ℕ) (ha : 2 ≤ a)
    (x f : QHilbert) (hf : f ∈ closureWithConstants) :
    ‖x - f‖ ^ 2 = (squareJumpFunctional a x) ^ 2 /
      (2 * zetaTwo * ((a : ℝ) ^ 4 - a + 1)) +
      ‖x - f - (squareJumpFunctional a x /
        (2 * zetaTwo * ((a : ℝ) ^ 4 - a + 1))) • squareJumpWitness a‖ ^ 2 := by
  have he : qDifference (x - f) (a ^ 2) - qDifference (x - f) a =
      squareJumpFunctional a x := by
    rw [← squareJumpFunctional_apply a ha, map_sub,
      squareJumpFunctional_zero_on_closureWithConstants a ha hf, sub_zero]
  rw [squareJump_energy_exact a ha (x - f), he]

theorem floorDilation_two_qOne_defect :
    squareJumpFunctional 2 (floorDilation 2 (by decide) qOne) = -1 := by
  rw [squareJumpFunctional_apply 2 (by decide)]
  simp only [qDifference, floorDilation_sequence, qSequence_qOne]
  norm_num [qOneSequence]

theorem floorDilation_two_qResidue_two_defect :
    squareJumpFunctional 2 (floorDilation 2 (by decide) (qResidue 2)) = -1 := by
  rw [squareJumpFunctional_apply 2 (by decide)]
  simp only [qDifference, floorDilation_sequence, qSequence_qResidue]
  norm_num [ArithmeticCumulative.residueFraction]

/-- A complete, positive separation bound; the additional term is exact. -/
theorem defect_neg_one_error_energy_exact (x f : QHilbert)
    (hx : squareJumpFunctional 2 x = -1) (hf : f ∈ closureWithConstants) :
    ‖x - f‖ ^ 2 = 1 / (30 * zetaTwo) +
      ‖x - f + (1 / (30 * zetaTwo)) • squareJumpWitness 2‖ ^ 2 := by
  rw [closureWithConstants_error_energy_exact 2 (by decide) x f hf, hx]
  norm_num only [Nat.cast_ofNat]
  rw [show 2 * zetaTwo * 15 = 30 * zetaTwo by ring]
  simp only [neg_div, neg_smul, sub_neg_eq_add]

theorem floorDilation_two_qOne_error_sq_lower_bound (f : QHilbert)
    (hf : f ∈ closureWithConstants) :
    1 / (30 * zetaTwo) ≤ ‖floorDilation 2 (by decide) qOne - f‖ ^ 2 := by
  rw [defect_neg_one_error_energy_exact _ f floorDilation_two_qOne_defect hf]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem floorDilation_two_qResidue_two_error_sq_lower_bound (f : QHilbert)
    (hf : f ∈ closureWithConstants) :
    1 / (30 * zetaTwo) ≤ ‖floorDilation 2 (by decide) (qResidue 2) - f‖ ^ 2 := by
  rw [defect_neg_one_error_energy_exact _ f floorDilation_two_qResidue_two_defect hf]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem floorDilation_two_qOne_not_mem :
    floorDilation 2 (by decide) qOne ∉ closureWithConstants := by
  intro h
  have hz := squareJumpFunctional_zero_on_closureWithConstants 2 (by decide) h
  rw [floorDilation_two_qOne_defect] at hz
  norm_num at hz

theorem floorDilation_two_qResidue_two_not_mem :
    floorDilation 2 (by decide) (qResidue 2) ∉ closureWithConstants := by
  intro h
  have hz := squareJumpFunctional_zero_on_closureWithConstants 2 (by decide) h
  rw [floorDilation_two_qResidue_two_defect] at hz
  norm_num at hz

theorem floorDilation_two_not_preserve_closureWithConstants :
    ¬ ∀ f ∈ closureWithConstants, floorDilation 2 (by decide) f ∈ closureWithConstants := by
  intro h
  exact floorDilation_two_qOne_not_mem (h qOne qOne_mem_closureWithConstants)

theorem floorDilation_two_not_preserve_squarefreeClosure :
    ¬ ∀ f ∈ ZetaTwoOptimizerStage.closure,
      floorDilation 2 (by decide) f ∈ ZetaTwoOptimizerStage.closure := by
  intro h
  exact floorDilation_two_qResidue_two_not_mem
    (closure_le_closureWithConstants
      (h (qResidue 2) QParityConditionalTarget.qResidue_two_mem_closure))

/-- The target itself passes this test; the obstruction concerns the dilation method. -/
theorem qTarget_two_squareJump_two :
    squareJumpFunctional 2 (qTarget 2 (by decide)) = 0 := by
  rw [squareJumpFunctional_apply 2 (by decide)]
  simp only [qDifference, qTarget_sequence]
  norm_num [Nat.log]

end RiemannResearch.RH.PrimePowerTarget
