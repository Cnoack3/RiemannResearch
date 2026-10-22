/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QParityConditionalTarget
import RiemannResearch.Analysis.ScreenedCarry

/-!
# The even-indicator closure obligation and its exact residual

Source: user-provided `Two_Prime_Mellin_Parity_Handoff_2026-10-20(1).md`,
Section 6.1. The identity E₂ = 1 - 2g₂ is an identity in the actual complete-Q
Hilbert space. It gives identical projection residuals for every projection
space containing the legal atom g₂, including the exhaustive squarefree
stages and their closed span. No closure membership is asserted unconditionally.
-/

noncomputable section
namespace RiemannResearch.RH.QEvenClosure
open ZetaTwoHilbert ZetaTwoParitySignal
open RiemannResearch.Analysis.ScreenedCarry

/-- Parity and the constant have the same membership obligation once g₂ is legal. -/
theorem qEven_mem_iff (V : Submodule ℝ QHilbert) (h2 : qResidue 2 ∈ V) :
    qEven ∈ V ↔ qOne ∈ V := by
  have hodd : qOdd ∈ V := V.smul_mem 2 h2
  constructor
  · intro h
    simpa only [qEven_add_qOdd] using V.add_mem h hodd
  · intro h
    exact V.sub_mem h hodd

/-- Exact equality of the actual screened vectors; no estimate or tail is lost. -/
theorem screen_qEven (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (h2 : qResidue 2 ∈ V) : screen V qEven = screen V qOne := by
  exact screen_sub_of_mem V qOne (V.smul_mem 2 h2)

/-- Both target errors have the same complete-Q squared norm. -/
theorem qEven_residual_norm_sq (V : Submodule ℝ QHilbert)
    [V.HasOrthogonalProjection] (h2 : qResidue 2 ∈ V) :
    ‖qEven - V.starProjection qEven‖ ^ 2 =
      ‖qOne - V.starProjection qOne‖ ^ 2 := by
  exact congrArg (fun x : QHilbert => ‖x‖ ^ 2) (screen_qEven V h2)

/-- The actual squarefree closed span has exactly the original constant obligation. -/
theorem qEven_mem_closure_iff :
    qEven ∈ ZetaTwoOptimizerStage.closure ↔
      qOne ∈ ZetaTwoOptimizerStage.closure :=
  qEven_mem_iff _ QParityConditionalTarget.qResidue_two_mem_closure

/-- Exact equality with the actual exhaustive finite-stage error. -/
theorem qEven_stage_error (n : ℕ) (hn : 0 < n) :
    ‖qEven - (ZetaTwoOptimizerStage.stage n).starProjection qEven‖ ^ 2 =
      ZetaTwoOptimizerStage.error n :=
  qEven_residual_norm_sq _ (QParityConditionalTarget.qResidue_two_mem_stage n hn)

/-- Exact equality of the two limiting residual vectors. -/
theorem qEven_limiting_residual :
    qEven - ZetaTwoOptimizerStage.closure.starProjection qEven =
      ZetaTwoOptimizerStage.limitingResidual :=
  screen_qEven _ QParityConditionalTarget.qResidue_two_mem_closure

end RiemannResearch.RH.QEvenClosure
