/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QReciprocalMellinCriterion
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Near-linear regularized reciprocal cost implies RH

Source: user-provided Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf,
Section 8.3, and the 8 November continuation of its research agenda.
The paper's O(alpha) cost criterion is strengthened here to
O_eta(alpha^(1-eta)) for every eta>0 along the explicit schedule
alpha_j=(j+1)^(-4). The Mellin criterion permits subpower unsmoothed norms.
This is a conditional research reduction. A complete-cost upper bound for
an actual legal family remains Open; no minimizing-family existence or
arithmetic cost estimate is inserted as an implicit assumption.

-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QReciprocalRegularizedCriterion
open ZetaTwoHilbert QShiftedReciprocal QReciprocalMellinCriterion

/-- The actual complete Q Tikhonov functional at the constant target. -/
def reciprocalCost (α : ℝ) (v : QHilbert) : ℝ :=
  ‖B (qOne - v)‖ ^ 2 + α * ‖v‖ ^ 2

/-- A fixed schedule making both approximation and energy budgets explicit. -/
def regularizationScale (j : ℕ) : ℝ := ((j : ℝ) + 1) ^ (-4 : ℝ)

theorem regularizationScale_pos (j : ℕ) : 0 < regularizationScale j := by
  unfold regularizationScale
  positivity

theorem reciprocalCost_nonneg (α : ℝ) (hα : 0 ≤ α) (v : QHilbert) :
    0 ≤ reciprocalCost α v := by
  unfold reciprocalCost
  positivity

/-- Arbitrarily small positive exponent losses in the regularized cost
are allowed. The cost is measured on the entire Q space. -/
theorem riemannHypothesis_of_near_linear_regularized_cost
    (U : ℕ → QHilbert) (hU : ∀ j, U j ∈ QFullResidueProjection.legalSpan)
    (hcost : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      reciprocalCost (regularizationScale j) (U j) ≤
        C * (regularizationScale j) ^ (1 - η)) :
    RiemannHypothesis := by
  have hcost' (η : ℝ) (hη : 0 < η) : ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      ‖B (qOne - U j)‖ ^ 2 + ((j : ℝ) + 1) ^ (-4 : ℝ) * ‖U j‖ ^ 2 ≤
        C * ((j : ℝ) + 1) ^ (-4 + 4 * η) := by
    obtain ⟨C, hC, h⟩ := hcost η hη
    refine ⟨C, hC, ?_⟩
    intro j
    have he : (regularizationScale j) ^ (1 - η) =
        ((j : ℝ) + 1) ^ (-4 + 4 * η) := by
      unfold regularizationScale
      rw [← Real.rpow_mul (by positivity : 0 ≤ (j : ℝ) + 1)]
      congr 1
      ring
    have hj := h j
    rw [he] at hj
    exact hj
  have hhead : Tendsto (fun j : ℕ => j + 1) atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ => show j ≤ j + 1 by omega) tendsto_id
  have hbase : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop.comp hhead :
        Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) atTop atTop)
  have hR : Tendsto (fun j : ℕ => ((j : ℝ) + 2) ^ 2 *
      ‖B (qOne - U j)‖ ^ 2) atTop (𝓝 0) := by
    obtain ⟨C, _hC, h⟩ := hcost' (1 / 4) (by norm_num)
    have hp : Tendsto (fun j : ℕ => ((j : ℝ) + 1) ^ (-1 : ℝ))
        atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp hbase
    have hu : Tendsto (fun j : ℕ => (4 * C) * ((j : ℝ) + 1) ^ (-1 : ℝ))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using hp.const_mul (4 * C)
    apply squeeze_zero (fun j => by positivity) ?_ hu
    intro j
    have hx : 0 < (j : ℝ) + 1 := by positivity
    have hc := h j
    norm_num only [show -(4 : ℝ) + 4 * (1 / 4) = -3 by norm_num] at hc
    have he : ‖B (qOne - U j)‖ ^ 2 ≤ C * ((j : ℝ) + 1) ^ (-3 : ℝ) := by
      have hpositive : 0 ≤ ((j : ℝ) + 1) ^ (-4 : ℝ) * ‖U j‖ ^ 2 := by positivity
      linarith only [hc, hpositive]
    have hhead_le : (j : ℝ) + 2 ≤ 2 * ((j : ℝ) + 1) := by
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have hhead2 := pow_le_pow_left₀ (by positivity : 0 ≤ (j : ℝ) + 2) hhead_le 2
    have hhead2' : ((j : ℝ) + 2) ^ 2 ≤ 4 * ((j : ℝ) + 1) ^ 2 := by
      nlinarith only [hhead2]
    calc
      _ ≤ (4 * ((j : ℝ) + 1) ^ 2) * ‖B (qOne - U j)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hhead2' (sq_nonneg _)
      _ ≤ (4 * ((j : ℝ) + 1) ^ 2) * (C * ((j : ℝ) + 1) ^ (-3 : ℝ)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = (4 * C) * (((j : ℝ) + 1) ^ 2 * ((j : ℝ) + 1) ^ (-3 : ℝ)) := by ring
      _ = _ := by
        rw [← Real.rpow_two, ← Real.rpow_add hx]
        norm_num
  have hG (a : ℝ) (ha : 0 < a) : Tendsto
      (fun j : ℕ => ((j : ℝ) + 1) ^ (-a) * ‖U j‖ ^ 2) atTop (𝓝 0) := by
    obtain ⟨C, _hC, h⟩ := hcost' (a / 8) (by linarith)
    have hp : Tendsto (fun j : ℕ => ((j : ℝ) + 1) ^ (-(a / 2)))
        atTop (𝓝 0) := (tendsto_rpow_neg_atTop (by linarith : 0 < a / 2)).comp hbase
    have hu : Tendsto (fun j : ℕ => C * ((j : ℝ) + 1) ^ (-(a / 2)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using hp.const_mul C
    apply squeeze_zero (fun j => by positivity) ?_ hu
    intro j
    have hx : 0 < (j : ℝ) + 1 := by positivity
    have hc := h j
    have he : ((j : ℝ) + 1) ^ (-4 : ℝ) * ‖U j‖ ^ 2 ≤
        C * ((j : ℝ) + 1) ^ (-4 + 4 * (a / 8)) := by
      linarith only [hc, sq_nonneg ‖B (qOne - U j)‖]
    calc
      _ = (((j : ℝ) + 1) ^ (4 - a) * ((j : ℝ) + 1) ^ (-4 : ℝ)) * ‖U j‖ ^ 2 := by
        rw [← Real.rpow_add hx]
        congr 2
        ring
      _ = ((j : ℝ) + 1) ^ (4 - a) * (((j : ℝ) + 1) ^ (-4 : ℝ) * ‖U j‖ ^ 2) := by ring
      _ ≤ ((j : ℝ) + 1) ^ (4 - a) *
          (C * ((j : ℝ) + 1) ^ (-4 + 4 * (a / 8))) :=
        mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hx.le _)
      _ = C * (((j : ℝ) + 1) ^ (4 - a) *
          ((j : ℝ) + 1) ^ (-4 + 4 * (a / 8))) := by ring
      _ = C * ((j : ℝ) + 1) ^ (-(a / 2)) := by
        rw [← Real.rpow_add hx]
        congr 2
        ring
  apply riemannHypothesis_of_variable_head_subpower_norm
    U hU (fun j => j + 1) (fun j => by omega) hhead
  · simpa only [Nat.cast_add, Nat.cast_one,
      show ∀ j : ℕ, (j : ℝ) + 1 + 1 = (j : ℝ) + 2 by intro j; ring] using hR
  · intro a ha
    simpa only [Nat.cast_add, Nat.cast_one] using hG a ha

end RiemannResearch.RH.QReciprocalRegularizedCriterion
