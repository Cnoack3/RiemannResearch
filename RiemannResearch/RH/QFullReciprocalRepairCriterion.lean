/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QTriangularWeightedBessel
import RiemannResearch.RH.QDisplacementTailTests
import RiemannResearch.RH.ParetoSquarefreeDampingConverse
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
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

namespace RiemannResearch.RH.QFullReciprocalHeadTail
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QShiftedReciprocal
open QFullResidueProjection QFullDisplacement QFiniteSupportDualCriterion

/-- The signed tail pairing has a fixed offset and is independent of the legal
interpolant. Only the tail pairing with the fixed reciprocal target varies. -/
theorem repair_tail_pairing_eq (N : ℕ) (F : QHilbert)
    (hF : F ∈ closure) (hhead : ∀ n < N, F n = B displacement n) :
    inner ℝ F (qResidual - finiteHead N qResidual) =
      inner ℝ (B displacement) (qResidual - finiteHead N qResidual) -
        ‖toPareto displacement‖ ^ 2 / zetaTwo := by
  have h := reciprocal_head_energy_identity N F hF hhead
  rw [inner_sub_left] at h
  have h' := (div_eq_iff zetaTwo_pos.ne').mpr (h.trans (mul_comm _ _))
  linarith only [h']

/-- Arbitrarily growing legal exact repairs give the same signed limit. -/
theorem repair_tail_pairing_tendsto {F : ℕ → QHilbert} (hF : ∀ N, F N ∈ closure)
    (hhead : ∀ N n, n < N → F N n = B displacement n) :
    Tendsto (fun N => inner ℝ (F N) (qResidual - finiteHead N qResidual)) atTop
      (𝓝 (-(‖toPareto displacement‖ ^ 2 / zetaTwo))) := by
  have ht : Tendsto (fun N => qResidual - finiteHead N qResidual) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds.sub (finiteHead_tendsto qResidual) :
        Tendsto (fun N => qResidual - finiteHead N qResidual) atTop
          (𝓝 (qResidual - qResidual)))
  have hi : Tendsto (fun N => inner ℝ (B displacement) (qResidual - finiteHead N qResidual))
      atTop (𝓝 (inner ℝ (B displacement) 0)) := tendsto_const_nhds.inner ht
  simp_rw [repair_tail_pairing_eq _ _ (hF _) (hhead _)]
  simpa only [inner_zero_right, zero_sub] using hi.sub_const (‖toPareto displacement‖ ^ 2 / zetaTwo)

/-- The signed error in measuring the limiting offset is at most the product
of both actual tails divided by N + 2, uniformly over all legal repairs. -/
theorem scaled_repair_tail_pairing_error_le (N : ℕ) (F : QHilbert)
    (hF : F ∈ closure) (hhead : ∀ j < N, F j = B displacement j) :
    ((N : ℝ) + 2) * |inner ℝ F (qResidual - finiteHead N qResidual) +
      ‖toPareto displacement‖ ^ 2 / zetaTwo| ≤
      ‖QAnnihilatorTailEscape.tail N displacement‖ * ‖qResidual - finiteHead N qResidual‖ := by
  rw [repair_tail_pairing_eq N F hF hhead, sub_add_cancel]
  let tail := QAnnihilatorTailEscape.tail N
  have ht (f : QHilbert) (j : ℕ) (hj : j < N) : tail f j = 0 := by
    change f j - finiteHead N f j = 0
    rw [finiteHead_apply_of_lt _ _ _ hj, sub_self]
  have hz (n : ℕ) (hn : n ≤ N) : qSequence (tail displacement) n = 0 := by
    cases n with
    | zero => rfl
    | succ j => rw [qSequence_succ, ht displacement j (Nat.lt_of_succ_le hn), zero_div]
  change ((N : ℝ) + 2) * |inner ℝ (B displacement) (tail qResidual)| ≤
    ‖tail displacement‖ * ‖tail qResidual‖
  rw [← QTriangularWeightedBessel.inner_B_tail_of_onset displacement (tail qResidual) N (ht qResidual)]
  calc
    _ ≤ ((N : ℝ) + 2) * (‖B (tail displacement)‖ * ‖tail qResidual‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (QSquarefreeDisplacementRegularity.scaled_B_norm_le_of_head _ N hz) (norm_nonneg _)

/-- Cofinal nonnegative signed repair pairings are equivalent to RH. -/
theorem riemannHypothesis_iff_frequently_nonneg_repair_tail
    {F : ℕ → QHilbert} (hF : ∀ N, F N ∈ closure)
    (hhead : ∀ N n, n < N → F N n = B displacement n) :
    RiemannHypothesis ↔ ∃ᶠ N : ℕ in atTop,
      0 ≤ inner ℝ (F N) (qResidual - finiteHead N qResidual) := by
  constructor
  · intro hRH
    have hmem : qOne ∈ closure := by
      apply squarefree_closure_le_full
      rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
      exact qSquarefreeClosure_iff_paretoSquarefreeClosure.mpr
        (Pareto.ResidueMellin.hilbertOne_mem_squarefreeClosure_of_riemannHypothesis hRH)
    have hr := qResidual_eq_zero_iff.mpr hmem
    have hd := displacement_eq_zero_of_qResidual_eq_zero hr
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro N
    rw [repair_tail_pairing_eq N (F N) (hF N) (hhead N), hd, map_zero, inner_zero_left]
    have hz : toPareto (0 : QHilbert) = 0 := toParetoCLM.map_zero
    simp [hz]
  · intro hsign
    apply riemannHypothesis_of_displacement_eq_zero
    by_contra hd
    have hnegative : -(‖toPareto displacement‖ ^ 2 / zetaTwo) < 0 :=
      neg_neg_of_pos (div_pos (displacement_p_energy_pos hd) zetaTwo_pos)
    exact hsign (((repair_tail_pairing_tendsto hF hhead).eventually (gt_mem_nhds hnegative)).mono
      fun _ hn => not_le_of_gt hn)

end RiemannResearch.RH.QFullReciprocalHeadTail
