/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullReciprocalRepairBudget
import RiemannResearch.RH.QFullReciprocalHeadTail
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual dilated Möbius repairs and the residual-tail RH criterion

Source: user-provided Reciprocal_Head_Investigation_2026-11-07.md, Section 8.
The explicit complete repair energy supplies the paper's budget-to-product
implication. The required joint decay remains an explicit Open provider.
The reciprocal multiplier R is the existing QShiftedReciprocal.B, distinct
from the density dQ/dP.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QFullDilatedMobiusRepair
open ZetaTwoHilbert ZetaTwoProbability QFullDisplacement
open QFullResidueProjection QFiniteSupportDualCriterion

/-- The actual complete repair norm and the actual residual-tail norm vanish
in product if the sharper complete Gram-trace budget has joint decay. -/
theorem reciprocalRepair_tail_product_of_trace
    (hdecay : Tendsto (fun N => gramTrace N *
      ‖qResidual - finiteHead N qResidual‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun N => ‖reciprocalRepair N displacement‖ *
      ‖qResidual - finiteHead N qResidual‖) atTop (𝓝 0) := by
  have hs : Tendsto (fun N => (‖reciprocalRepair N displacement‖ *
      ‖qResidual - finiteHead N qResidual‖) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _)
    · intro N
      have h := mul_le_mul_of_nonneg_right
        (reciprocalRepair_norm_sq_le_trace N displacement)
        (sq_nonneg ‖qResidual - finiteHead N qResidual‖)
      simpa only [mul_pow, mul_assoc] using h
    · have h := hdecay.const_mul (4 * zetaTwo * ‖displacement‖ ^ 2)
      simp only [mul_zero] at h
      exact h.congr' (Eventually.of_forall fun N => by ring)
  have h := hs.sqrt
  simpa only [Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    Real.sqrt_zero] using h

/-- The paper's explicit K_N budget is sufficient; no repair choice is opaque. -/
theorem reciprocalRepair_tail_product_of_budget
    (hdecay : Tendsto (fun N => dilationBudget N *
      ‖qResidual - finiteHead N qResidual‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun N => ‖reciprocalRepair N displacement‖ *
      ‖qResidual - finiteHead N qResidual‖) atTop (𝓝 0) := by
  apply reciprocalRepair_tail_product_of_trace
  refine squeeze_zero (fun N => mul_nonneg (gramTrace_nonneg N) (sq_nonneg _))
    (fun N => mul_le_mul_of_nonneg_right (gramTrace_le_dilationBudget N)
      (sq_nonneg _)) hdecay

/-- Conditional research reduction: actual Gram-trace/residual-tail decay
forces the actual matched displacement to vanish. The decay provider is Open. -/
theorem displacement_eq_zero_of_gramTrace_tail_decay
    (hdecay : Tendsto (fun N => gramTrace N *
      ‖qResidual - finiteHead N qResidual‖ ^ 2) atTop (𝓝 0)) :
    displacement = 0 :=
  QFullReciprocalHeadTail.displacement_eq_zero_of_repair_norm_tail_product
    (fun N => show reciprocalRepair N displacement ∈ closure from
      (show reciprocalRepair N displacement ∈
        _root_.closure (legalSpan : Set QHilbert) from
        subset_closure (reciprocalRepair_mem N displacement)))
    (fun N n hn => reciprocalRepair_head N displacement n hn)
    (reciprocalRepair_tail_product_of_trace hdecay)

/-- Conditional research reduction: the explicit complete K_N-tail product
implies Mathlib's Riemann Hypothesis. Its arithmetic provider remains Open. -/
theorem riemannHypothesis_of_dilationBudget_tail_decay
    (hdecay : Tendsto (fun N => dilationBudget N *
      ‖qResidual - finiteHead N qResidual‖ ^ 2) atTop (𝓝 0)) :
    RiemannHypothesis :=
  QFullReciprocalHeadTail.riemannHypothesis_of_repair_norm_tail_product
    (fun N => show reciprocalRepair N displacement ∈ closure from
      (show reciprocalRepair N displacement ∈
        _root_.closure (legalSpan : Set QHilbert) from
        subset_closure (reciprocalRepair_mem N displacement)))
    (fun N n hn => reciprocalRepair_head N displacement n hn)
    (reciprocalRepair_tail_product_of_budget hdecay)

end RiemannResearch.RH.QFullDilatedMobiusRepair
