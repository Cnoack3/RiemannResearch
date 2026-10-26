/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QHeadCrossMoments
import RiemannResearch.RH.QHeadCrossEnvelope
import RiemannResearch.RH.QSquarefreeCRTCrossCriterion
import RiemannResearch.RH.QSquarefreeCRTResponse
import RiemannResearch.RH.QSquarefreeMovingHeadEnergy
import RiemannResearch.RH.QReciprocalConditioning
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.RH.QTriangularCharge
import RiemannResearch.Analysis.LogTailWeights
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Actual squarefree CRT cumulative-moment criterion

Source: the user's infinite-CRT weighted-energy handoff, priority 2,
26 October 2026. Ordinary Q orthogonality gives an exact completed square for
every cumulative cross moment. A cofinal upper bound on the positive Abel
variation suffices for RH. That arithmetic upper-bound provider remains Open.
Factorial moduli supply the common-conductor condition unconditionally.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeCRTAbelCriterion
open ZetaTwoHilbert ZetaTwoProbability QAnnihilatorTailEscape
open QReciprocalConditioning QSquarefreeCRTResponse QSquarefreeSmoothedProjection
open QPolylogTailEnergy QHeadCrossMoments QSquarefreeCRTCrossCriterion
open RiemannResearch.Analysis.LogTailWeights

theorem movingCorrection_inner_conditionedRemainder_zero
    (N L : ℕ) (hL : 0 < L)
    (hdiv : ∀ i : Fin N, Squarefree (i.val + 2) → i.val + 2 ∣ L) :
    inner ℝ (movingCorrection N) (conditionedRemainder N L hL) = 0 := by
  have hm : movingCorrection N ∈ ZetaTwoOptimizerStage.stage N := by
    rw [movingCorrection_eq_conditioned_projection N L hL hdiv]
    exact (ZetaTwoOptimizerStage.stage N).starProjection_apply_mem _
  exact Submodule.inner_right_of_mem_orthogonal hm
    (conditionedRemainder_mem_orthogonal N L hL hdiv)

/-- Every actual cumulative moment retains its nonnegative square remainder. -/
theorem conditioned_headCross_completed_square
    (N L H : ℕ) (hL : 0 < L)
    (hdiv : ∀ i : Fin N, Squarefree (i.val + 2) → i.val + 2 ∣ L) :
    headCross H (movingCorrection N) (conditionedRemainder N L hL) =
      ‖tail H (movingCorrection N) - (1 / 2 : ℝ) •
        tail H (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N))‖ ^ 2 -
      ‖tail H (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N))‖ ^ 2 / 4 := by
  exact headCross_completed_square H (movingCorrection N)
    (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N))
    (movingCorrection_inner_conditionedRemainder_zero N L hL hdiv)

/-- A common endpoint budget for every stage, head, modulus, and profile exponent. -/
theorem conditioned_source_endpoint_le_half (k N L H : ℕ) (hL : 0 < L) :
    polylogTailProfile k H *
      ‖tail H (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N))‖ ^ 2 / 4 ≤
        (1 / 2 : ℝ) := by
  have hb (n : ℕ) :
      |qSequence (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N)) n| ≤
        Real.sqrt zetaTwo := by
    have hc := conditionalReciprocal_bound L hL (ZetaTwoOptimizerStage.residual N) n
    have hm := mul_le_mul_of_nonneg_left
      (QTriangularCharge.residual_norm_le_one N) (Real.sqrt_nonneg zetaTwo)
    exact hc.trans (by simpa only [mul_one] using hm)
  have htail := scaled_tail_energy_le_of_bounded
    (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N)) H
    (Real.sqrt zetaTwo) (Real.sqrt_nonneg zetaTwo) hb
  have htwo : (H : ℝ) *
      ‖tail H (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N))‖ ^ 2 ≤ 2 := by
    calc
      _ ≤ 2 * (Real.sqrt zetaTwo) ^ 2 / zetaTwo := htail
      _ = 2 := by
        rw [Real.sq_sqrt zetaTwo_pos.le]
        field_simp [zetaTwo_pos.ne']
  have hp : polylogTailProfile k H ≤ (H : ℝ) :=
    (polylogTailProfile_le_logWeight k H).trans (logWeight_le_nat k H)
  have hm := mul_le_mul_of_nonneg_right hp
    (sq_nonneg ‖tail H (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N))‖)
  linarith

/-- Ordinary Q orthogonality controls the endpoint. Only the positive
cumulative variation still requires an arithmetic estimate. -/
theorem conditioned_cross_lower_of_positive_variation
    (k N L H : ℕ) (hL : 0 < L)
    (hdiv : ∀ i : Fin N, Squarefree (i.val + 2) → i.val + 2 ∣ L) :
    -(1 / 2 : ℝ) -
      positiveCrossVariation k H (movingCorrection N) (conditionedRemainder N L hL) ≤
        weightedHeadCross k H (movingCorrection N) (conditionedRemainder N L hL) := by
  have h := weightedHeadCross_lower_of_positive_variation k H (movingCorrection N)
    (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N))
    (movingCorrection_inner_conditionedRemainder_zero N L hL hdiv)
  have he := conditioned_source_endpoint_le_half k N L H hL
  change -(polylogTailProfile k H *
      ‖tail H (conditionalReciprocal L hL (ZetaTwoOptimizerStage.residual N))‖ ^ 2 / 4) -
    positiveCrossVariation k H (movingCorrection N) (conditionedRemainder N L hL) ≤
      weightedHeadCross k H (movingCorrection N) (conditionedRemainder N L hL) at h
  linarith

theorem energy_le_of_positive_variation
    (N L H : ℕ) (hL : 0 < L)
    (hdiv : ∀ i : Fin N, Squarefree (i.val + 2) → i.val + 2 ∣ L)
    (A : ℝ)
    (hA : positiveCrossVariation 2 H (movingCorrection N)
      (conditionedRemainder N L hL) ≤ A) :
    weightedHeadEnergy 2 H (movingCorrection N) ≤ sourceBudget + 1 + 2 * A := by
  have hc := conditioned_cross_lower_of_positive_variation 2 N L H hL hdiv
  have he := energy_le_of_cross_lower N L H hL (A + 1 / 2) (by linarith)
  linarith

/-- Conditional research reduction: one divergent head and cofinally bounded
positive Abel variation suffice. The variation bound remains Open. -/
theorem riemannHypothesis_of_frequently_positive_variation_bound
    (H L : ℕ → ℕ) (hH : Tendsto H atTop atTop) (hL : ∀ N, 0 < L N)
    (hdiv : ∀ N, ∀ i : Fin N, Squarefree (i.val + 2) → i.val + 2 ∣ L N)
    (A : ℝ) (hA : ∃ᶠ N : ℕ in atTop,
      positiveCrossVariation 2 (H N) (movingCorrection N)
        (conditionedRemainder N (L N) (hL N)) ≤ A) : RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_cross_lower H L hH hL (A + 1 / 2)
  exact hA.mono (fun N hn => by
    have hc := conditioned_cross_lower_of_positive_variation
      2 N (L N) (H N) (hL N) (hdiv N)
    linarith)

/-- If the actual residual is nonzero, the missing positive-variation budget
fails along every divergent physical head and every common-modulus schedule. -/
theorem positive_variation_tendsto_atTop_of_residual_ne_zero
    (H L : ℕ → ℕ) (hH : Tendsto H atTop atTop) (hL : ∀ N, 0 < L N)
    (hdiv : ∀ N, ∀ i : Fin N, Squarefree (i.val + 2) → i.val + 2 ∣ L N)
    (hr : ZetaTwoOptimizerStage.limitingResidual ≠ 0) :
    Tendsto (fun N => positiveCrossVariation 2 (H N) (movingCorrection N)
      (conditionedRemainder N (L N) (hL N))) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  have hg := QSquarefreeMovingHeadEnergy.moving_head_energy_tendsto_atTop_of_residual_ne_zero
    2 H hH hr
  filter_upwards [hg.eventually (eventually_ge_atTop (sourceBudget + 1 + 2 * C))] with N hN
  have he := energy_le_of_positive_variation N (L N) (H N) (hL N) (hdiv N)
    (positiveCrossVariation 2 (H N) (movingCorrection N)
      (conditionedRemainder N (L N) (hL N))) le_rfl
  linarith

/-- A concrete common modulus; no prime enumeration or squarefree-product
assumption is needed for the CRT orthogonality argument. -/
theorem stage_conductor_dvd_factorial (N : ℕ) (i : Fin N) :
    i.val + 2 ∣ (N + 1).factorial := by
  exact Nat.dvd_factorial (by omega) (by have hi := i.isLt; omega)

theorem riemannHypothesis_of_frequently_factorial_positive_variation_bound
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (A : ℝ) (hA : ∃ᶠ N : ℕ in atTop,
      positiveCrossVariation 2 (H N) (movingCorrection N)
        (conditionedRemainder N (N + 1).factorial
          (Nat.factorial_pos _)) ≤ A) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_frequently_positive_variation_bound
    H (fun N => (N + 1).factorial) hH (fun N => Nat.factorial_pos _)
    (fun N i _ => stage_conductor_dvd_factorial N i) A hA


/-- A concrete one-sided cumulative-moment estimate gives an explicit budget. -/
theorem energy_le_of_reciprocal_envelope
    (N L H : ℕ) (hL : 0 < L)
    (hdiv : ∀ i : Fin N, Squarefree (i.val + 2) → i.val + 2 ∣ L)
    (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ t : ℕ, 0 < t → t < H →
      headCross t (movingCorrection N) (conditionedRemainder N L hL) ≤
        C / ((t : ℝ) + 1)) :
    weightedHeadEnergy 2 H (movingCorrection N) ≤ (4 + 2*C) / 3 := by
  have hv := positiveCrossVariation_le_third_of_reciprocal_envelope
    H (movingCorrection N) (conditionedRemainder N L hL) C hC hM
  have he := energy_le_of_positive_variation N L H hL hdiv (C/3) hv
  have hD : sourceBudget ≤ (1 : ℝ)/3 := reciprocalCrossBudget_le_third
  linarith

/-- Conditional research reduction with every CRT modulus supplied explicitly.
The sole arithmetic provider still needed is the one-sided reciprocal envelope,
on one divergent head, at arbitrarily large stages. -/
theorem riemannHypothesis_of_frequently_reciprocal_cumulative_bound
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∃ᶠ N : ℕ in atTop, ∀ t : ℕ, 0 < t → t < H N →
      headCross t (movingCorrection N)
        (conditionedRemainder N (N + 1).factorial (Nat.factorial_pos _)) ≤
          C / ((t : ℝ) + 1)) : RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_factorial_positive_variation_bound H hH (C/3)
  exact hM.mono (fun N hn =>
    positiveCrossVariation_le_third_of_reciprocal_envelope (H N)
      (movingCorrection N)
      (conditionedRemainder N (N + 1).factorial (Nat.factorial_pos _)) C hC hn)

end RiemannResearch.RH.QSquarefreeCRTAbelCriterion
