/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.Analysis.ResidualGainProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Exact squarefree Q relative-gain saturation

Source: user-requested conversion of the full Pareto projection theory,
17 October 2026. The existing residual-gain product theorem is applied to
the actual exhaustive squarefree Q optimizer. The stage dictionary is
masked at nonsquarefree conductors, so those stages have zero innovation.
No positive Schur denominator is asserted for a masked-out atom.

This is an exact geometric equivalence. Nonsummability of the actual
relative gains remains an open arithmetic obligation.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QSquarefreeRelativeGain
open ZetaTwoHilbert ZetaTwoOptimizerStage
open RiemannResearch.Analysis.ExhaustiveWalk

def gain (n : ℕ) : ℝ := ‖optimizer (n + 1) - optimizer n‖ ^ 2
def relativeGain (n : ℕ) : ℝ := gain n / error n

/-- Exact Pythagorean accounting, including the complete innovation norm. -/
theorem error_step (n : ℕ) : error n = error (n + 1) + gain n :=
  walkError_step squarefreeAtom id qOne n

theorem error_zero : error 0 = 1 := by
  have h : optimizer 0 = 0 := by simp [optimizer, stage, walkSpan]
  change ‖qOne - optimizer 0‖ ^ 2 = 1
  rw [h, sub_zero, qOne_norm_sq]

theorem relativeGain_nonneg (n : ℕ) : 0 ≤ relativeGain n :=
  div_nonneg (sq_nonneg _) (error_pos n).le

theorem relativeGain_lt_one (n : ℕ) : relativeGain n < 1 := by
  unfold relativeGain
  apply (div_lt_iff₀ (error_pos n)).mpr
  have hs := error_step n
  have hp := error_pos (n + 1)
  linarith

theorem error_relativeGain_step (n : ℕ) :
    error (n + 1) = error n * (1 - relativeGain n) := by
  have hcancel : error n * relativeGain n = gain n := by
    unfold relativeGain
    field_simp [ne_of_gt (error_pos n)]
  have hs := error_step n
  nlinarith

/-- Exact finite product; no limit or convergence is assumed. -/
theorem error_eq_product (n : ℕ) :
    error n = ∏ j ∈ Finset.range n, (1 - relativeGain j) := by
  have h := RiemannResearch.Analysis.ResidualGain.recurrence_eq_mul_product
    error_relativeGain_step n
  simpa only [error_zero, RiemannResearch.Analysis.ResidualGain.survivalProduct,
    one_mul] using h

/-- Exact finite additive accounting in the actual Q metric. -/
theorem error_eq_one_sub_gain_sum (n : ℕ) :
    error n = 1 - ∑ j ∈ Finset.range n, gain j := by
  have h := accumulated_gain squarefreeAtom id qOne n
  change (∑ j ∈ Finset.range n, gain j) = error 0 - error n at h
  rw [error_zero] at h
  linarith

/-- Squarefree closure is equivalent to divergence of the actual relative
gain sum; its divergence is not established by the product identity. -/
theorem closure_iff_relativeGain_not_summable :
    qOne ∈ ZetaTwoOptimizerStage.closure ↔ ¬Summable relativeGain :=
  error_tendsto_zero_iff_mem_closure.symm.trans
    (RiemannResearch.Analysis.ResidualGain.residual_tendsto_zero_iff_not_summable
      (error_pos 0) relativeGain_nonneg relativeGain_lt_one error_relativeGain_step)

/-- Masking a nonsquarefree conductor leaves the finite stage unchanged. -/
theorem stage_succ_eq_of_not_squarefree (n : ℕ) (hn : ¬Squarefree (n + 2)) :
    stage (n + 1) = stage n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i.val < n
    · exact Submodule.subset_span ⟨⟨i.val, hi⟩, rfl⟩
    · have he : i.val = n := by omega
      change squarefreeAtom i.val ∈ stage n
      rw [he, squarefreeAtom, if_neg hn]
      exact Submodule.zero_mem _
  · exact walkSpan_mono squarefreeAtom id (Nat.le_succ n)

/-- No division by a vanishing Schur innovation is used at omitted sites. -/
theorem relativeGain_eq_zero_of_not_squarefree (n : ℕ)
    (hn : ¬Squarefree (n + 2)) : relativeGain n = 0 := by
  have hs := stage_succ_eq_of_not_squarefree n hn
  simp only [relativeGain, gain, optimizer, hs, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_div]

/-- Conditional RH reduction; the actual nonsummability input remains Open. -/
theorem riemannHypothesis_of_relativeGain_not_summable
    (h : ¬Summable relativeGain) : RiemannHypothesis :=
  ZetaTwoParetoTransfer.riemannHypothesis_of_qOne_mem_squarefree_closure
    (closure_iff_relativeGain_not_summable.mpr h)

end RiemannResearch.RH.QSquarefreeRelativeGain
