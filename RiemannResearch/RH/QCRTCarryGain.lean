/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ScreenedBlockGain
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.QCRTCarryBlockBridge
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Literal CRT scores and the actual complete-Q stage gain

Source: Christian Noack's CRT-carry handoff, 19 October 2026, Sections 9--10.
The generic nested-projection trace inequality removes the previous need
to assume linear independence merely to lower-bound the actual stage gain.
Every old nontrivial divisor occurs, including composite divisors. The
statements allow the empty block and retain the separate new-prime gain.

The supplied orthogonal-projection instances concern finite divisor spans;
they are analytic infrastructure, not an assumed arithmetic score bound.
No lower bound on the growing-family scores and no RH conclusion is assumed
or proved here.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QCRTCarryGain

open ZetaTwoHilbert ZetaTwoProbability QCRTCarry QCRTCarryBlockBridge
open QCarryScreenedBlock (BlockIndex extendedOldStage)
open QSquarefreeLatticePackets (divisorStage)
open RiemannResearch.Analysis.ScreenedCarry

private theorem nestedGain (V W : Submodule ℝ QHilbert)
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hVW : V ≤ W) (x : QHilbert) :
    ‖screen V x‖ ^ 2 - ‖screen W x‖ ^ 2 =
      ‖W.starProjection x - V.starProjection x‖ ^ 2 := by
  have h := RiemannResearch.Analysis.ExhaustiveWalk.nested_projection_energy V W hVW x
  change ‖screen V x‖ ^ 2 = ‖screen W x‖ ^ 2 +
    ‖W.starProjection x - V.starProjection x‖ ^ 2 at h
  linarith

/-- The complete-Q conductor upper bound for the screened Gram trace. -/
def traceCap (L p : ℕ) : ℝ :=
  (2 / (zetaTwo * (p : ℝ))) * ∑ d : BlockIndex L, 1 / (d.val : ℝ)

private theorem prime_mem_extended (L p : ℕ) :
    qResidue p ∈ extendedOldStage L p := by
  unfold extendedOldStage
  exact (show Submodule.span ℝ {qResidue p} ≤
    divisorStage L ⊔ Submodule.span ℝ {qResidue p}
    from le_sup_right) (Submodule.subset_span (by simp))

private theorem divisor_mem_extended (L p : ℕ) (d : BlockIndex L) :
    qResidue d.val ∈ extendedOldStage L p := by
  unfold extendedOldStage
  apply (show divisorStage L ≤
    divisorStage L ⊔ Submodule.span ℝ {qResidue p}
    from le_sup_left)
  exact Submodule.subset_span
    ⟨d.val, (Nat.mem_divisors.mp (Finset.mem_filter.mp d.property).1).1, rfl⟩

theorem literal_trace_le_cap (L p : ℕ) (hp : p.Prime)
    [(extendedOldStage L p).HasOrthogonalProjection]
    (a b t : BlockIndex L → ℤ)
    (hcrt : ∀ d, (a d : ℝ) * (d.val : ℝ) + (b d : ℝ) * (p : ℝ) =
      1 + (t d : ℝ) * (p : ℝ) * (d.val : ℝ)) :
    (∑ d : BlockIndex L,
      ‖screen (extendedOldStage L p) (qCarry p d.val (a d) (b d))‖ ^ 2) ≤
        traceCap L p := by
  exact literal_complete_trace_bound (extendedOldStage L p) p
    (fun d : BlockIndex L => d.val) a b t
    (prime_mem_extended L p) (divisor_mem_extended L p) hp.two_le
    (fun d => by have hd := (Finset.mem_filter.mp d.property).2; omega) hcrt

/-- Scores of the full literal floor family control the actual carry-block
projection gain. No independence, inverse Gram matrix, or nonempty-block
assumption is required. -/
theorem literal_scores_le_actual_block_gain (L p : ℕ) (hL : 0 < L)
    (hp : p.Prime)
    [(extendedOldStage L p).HasOrthogonalProjection]
    [(divisorStage (p * L)).HasOrthogonalProjection]
    (a b t : BlockIndex L → ℤ)
    (hcrt : ∀ d, (a d : ℝ) * (d.val : ℝ) + (b d : ℝ) * (p : ℝ) =
      1 + (t d : ℝ) * (p : ℝ) * (d.val : ℝ)) :
    (∑ d : BlockIndex L,
      (inner ℝ (screen (extendedOldStage L p)
        (qCarry p d.val (a d) (b d)))
        (screen (extendedOldStage L p) qOne)) ^ 2) ≤
      traceCap L p *
        (‖screen (extendedOldStage L p) qOne‖ ^ 2 -
          ‖screen (divisorStage (p * L)) qOne‖ ^ 2) := by
  have hspan := literal_full_prime_block_stage L p hL hp a b t hcrt
  have hVU : extendedOldStage L p ≤ divisorStage (p * L) := by
    rw [← hspan]
    exact le_sup_left
  have hκ : ∀ d : BlockIndex L,
      qCarry p d.val (a d) (b d) ∈ divisorStage (p * L) := by
    intro d
    rw [← hspan]
    exact (show Submodule.span ℝ
      (Set.range (fun d : BlockIndex L => qCarry p d.val (a d) (b d))) ≤
      extendedOldStage L p ⊔ Submodule.span ℝ
        (Set.range (fun d : BlockIndex L => qCarry p d.val (a d) (b d)))
      from le_sup_right) (Submodule.subset_span ⟨d, rfl⟩)
  have hs := block_score_le_trace_mul_gain (extendedOldStage L p)
    (divisorStage (p * L)) hVU qOne
    (fun d : BlockIndex L => qCarry p d.val (a d) (b d)) hκ
  have hg : 0 ≤ ‖screen (extendedOldStage L p) qOne‖ ^ 2 -
      ‖screen (divisorStage (p * L)) qOne‖ ^ 2 := by
    rw [nestedGain (extendedOldStage L p) (divisorStage (p * L))
      hVU qOne]
    exact sq_nonneg _
  exact hs.trans (mul_le_mul_of_nonneg_right (literal_trace_le_cap L p hp a b t hcrt) hg)

/-- The whole stage gain is the sum of two actual nonnegative projection
increments: the new prime first, then every composite carry direction. -/
theorem stage_gain_eq_prime_add_block (L p : ℕ) (hL : 0 < L)
    (hp : p.Prime)
    [(divisorStage L).HasOrthogonalProjection]
    [(extendedOldStage L p).HasOrthogonalProjection]
    [(divisorStage (p * L)).HasOrthogonalProjection] :
    ‖screen (divisorStage L) qOne‖ ^ 2 -
      ‖screen (divisorStage (p * L)) qOne‖ ^ 2 =
      ‖(extendedOldStage L p).starProjection qOne -
          (divisorStage L).starProjection qOne‖ ^ 2 +
        ‖(divisorStage (p * L)).starProjection qOne -
          (extendedOldStage L p).starProjection qOne‖ ^ 2 := by
  have hOld : divisorStage L ≤ extendedOldStage L p := le_sup_left
  have hExt : extendedOldStage L p ≤ divisorStage (p * L) := by
    rw [← QCarryScreenedBlock.raw_prime_block_stage L p hL hp]
    exact le_sup_left
  have h₁ := nestedGain (divisorStage L) (extendedOldStage L p) hOld qOne
  have h₂ := nestedGain (extendedOldStage L p) (divisorStage (p * L)) hExt qOne
  linarith

/-- The carry-only score bound also bounds the complete stage gain, which
includes the separate new-prime improvement. -/
theorem literal_scores_le_total_stage_gain (L p : ℕ) (hL : 0 < L)
    (hp : p.Prime)
    [(divisorStage L).HasOrthogonalProjection]
    [(extendedOldStage L p).HasOrthogonalProjection]
    [(divisorStage (p * L)).HasOrthogonalProjection]
    (a b t : BlockIndex L → ℤ)
    (hcrt : ∀ d, (a d : ℝ) * (d.val : ℝ) + (b d : ℝ) * (p : ℝ) =
      1 + (t d : ℝ) * (p : ℝ) * (d.val : ℝ)) :
    (∑ d : BlockIndex L,
      (inner ℝ (screen (extendedOldStage L p)
        (qCarry p d.val (a d) (b d)))
        (screen (extendedOldStage L p) qOne)) ^ 2) ≤
      traceCap L p *
        (‖screen (divisorStage L) qOne‖ ^ 2 -
          ‖screen (divisorStage (p * L)) qOne‖ ^ 2) := by
  have hT : 0 ≤ traceCap L p :=
    (Finset.sum_nonneg (fun d _ => sq_nonneg _)).trans
      (literal_trace_le_cap L p hp a b t hcrt)
  have hOld : divisorStage L ≤ extendedOldStage L p := le_sup_left
  have hprime : 0 ≤ ‖screen (divisorStage L) qOne‖ ^ 2 -
      ‖screen (extendedOldStage L p) qOne‖ ^ 2 := by
    rw [nestedGain (divisorStage L) (extendedOldStage L p) hOld qOne]
    exact sq_nonneg _
  have hdiff : ‖screen (extendedOldStage L p) qOne‖ ^ 2 -
      ‖screen (divisorStage (p * L)) qOne‖ ^ 2 ≤
      ‖screen (divisorStage L) qOne‖ ^ 2 -
        ‖screen (divisorStage (p * L)) qOne‖ ^ 2 := by linarith
  exact (literal_scores_le_actual_block_gain L p hL hp a b t hcrt).trans
    (mul_le_mul_of_nonneg_left hdiff hT)

/-- A practical lower certificate retains the exact new-prime gain before
adding the trace lower bound for the full carry block. -/
theorem prime_gain_add_score_div_le_total_gain (L p : ℕ) (hL : 0 < L)
    (hp : p.Prime)
    [(divisorStage L).HasOrthogonalProjection]
    [(extendedOldStage L p).HasOrthogonalProjection]
    [(divisorStage (p * L)).HasOrthogonalProjection]
    (a b t : BlockIndex L → ℤ)
    (hcrt : ∀ d, (a d : ℝ) * (d.val : ℝ) + (b d : ℝ) * (p : ℝ) =
      1 + (t d : ℝ) * (p : ℝ) * (d.val : ℝ))
    (hT : 0 < traceCap L p) :
    ‖(extendedOldStage L p).starProjection qOne -
        (divisorStage L).starProjection qOne‖ ^ 2 +
      (∑ d : BlockIndex L,
        (inner ℝ (screen (extendedOldStage L p)
          (qCarry p d.val (a d) (b d)))
          (screen (extendedOldStage L p) qOne)) ^ 2) / traceCap L p ≤
      ‖screen (divisorStage L) qOne‖ ^ 2 -
        ‖screen (divisorStage (p * L)) qOne‖ ^ 2 := by
  have hs := literal_scores_le_actual_block_gain L p hL hp a b t hcrt
  have hdiv : (∑ d : BlockIndex L,
      (inner ℝ (screen (extendedOldStage L p)
        (qCarry p d.val (a d) (b d)))
        (screen (extendedOldStage L p) qOne)) ^ 2) / traceCap L p ≤
      ‖screen (extendedOldStage L p) qOne‖ ^ 2 -
        ‖screen (divisorStage (p * L)) qOne‖ ^ 2 := by
    apply (div_le_iff₀ hT).mpr
    nlinarith
  have hOld : divisorStage L ≤ extendedOldStage L p := le_sup_left
  have hprime := nestedGain (divisorStage L) (extendedOldStage L p) hOld qOne
  linarith

end RiemannResearch.RH.QCRTCarryGain
