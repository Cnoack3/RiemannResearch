/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.Analysis.ProjectionTrialEnergy
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Change of measure for projections onto the same closed physical subspace

The membership equivalence is explicit: no change of dictionary or arithmetic
closure hypothesis is hidden. The two projections may differ. Exact comparison
retains both their displacement and the full reciprocal metric correction.
-/

noncomputable section
namespace RiemannResearch.RH.QParetoClosedProjectionComparison
open Pareto ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer
open QParetoEquivalence QParetoMetric
open RiemannResearch.Analysis

variable (S : Submodule ℝ QHilbert) (T : Submodule ℝ ThresholdHilbert)
variable [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]

def qFit (x : QHilbert) : QHilbert := S.starProjection x

/-- The Pareto orthogonal projection, represented in Q coordinates. -/
def pFit (x : QHilbert) : QHilbert := toQ (T.starProjection (toPareto x))

@[simp] theorem toPareto_pFit (x : QHilbert) :
    toPareto (pFit T x) = T.starProjection (toPareto x) :=
  toPareto_toQ _

theorem toPareto_sub (x y : QHilbert) :
    toPareto (x - y) = toPareto x - toPareto y :=
  toParetoLinear.map_sub x y

variable (hsame : ∀ f : QHilbert, toPareto f ∈ T ↔ f ∈ S)
include hsame

omit [S.HasOrthogonalProjection] in
theorem pFit_mem (x : QHilbert) : pFit T x ∈ S := by
  apply (hsame _).mp
  rw [toPareto_pFit]
  exact T.starProjection_apply_mem _

omit [T.HasOrthogonalProjection] in
theorem toPareto_qFit_mem (x : QHilbert) : toPareto (qFit S x) ∈ T :=
  (hsame _).mpr (S.starProjection_apply_mem x)

/-- The Q error of the Pareto optimizer includes its Q displacement. -/
theorem q_trial_identity (x : QHilbert) :
    ‖x - pFit T x‖ ^ 2 = ‖x - qFit S x‖ ^ 2 +
      ‖qFit S x - pFit T x‖ ^ 2 := by
  exact projection_trial_energy S x (pFit T x) (pFit_mem S T hsame x)

/-- The Pareto error of the Q optimizer includes its Pareto displacement. -/
theorem p_trial_identity (x : QHilbert) :
    ‖toPareto (x - qFit S x)‖ ^ 2 =
      ‖toPareto (x - pFit T x)‖ ^ 2 +
      ‖toPareto (qFit S x - pFit T x)‖ ^ 2 := by
  have h := projection_trial_energy T (toPareto x) (toPareto (qFit S x))
    (toPareto_qFit_mem S T hsame x)
  rw [norm_sub_rev (T.starProjection (toPareto x))] at h
  simpa only [toPareto_sub, toPareto_pFit] using h

/-- Exact lower comparison for arbitrary closed dictionaries, not just finite fits. -/
theorem error_lower_identity (x : QHilbert) :
    zetaTwo * ‖x - qFit S x‖ ^ 2 =
      ‖toPareto (x - pFit T x)‖ ^ 2 +
      ‖toPareto (qFit S x - pFit T x)‖ ^ 2 +
      metricCorrection (x - qFit S x) := by
  rw [norm_identity, p_trial_identity S T hsame]

/-- Reversing the competitor retains its complete Q displacement. -/
theorem error_upper_identity (x : QHilbert) :
    ‖toPareto (x - pFit T x)‖ ^ 2 + metricCorrection (x - pFit T x) =
      zetaTwo * ‖x - qFit S x‖ ^ 2 +
      zetaTwo * ‖qFit S x - pFit T x‖ ^ 2 := by
  rw [← norm_identity, q_trial_identity S T hsame, mul_add]

/-- Moving from the Pareto optimizer to the Q optimizer strictly decreases the
reciprocal correction unless the two physical projections agree. -/
theorem correction_difference_exact (x : QHilbert) :
    metricCorrection (x - pFit T x) - metricCorrection (x - qFit S x) =
      ‖toPareto (qFit S x - pFit T x)‖ ^ 2 +
      zetaTwo * ‖qFit S x - pFit T x‖ ^ 2 := by
  linarith [error_lower_identity S T hsame x, error_upper_identity S T hsame x]

theorem error_strict (x : QHilbert) (hx : x ≠ qFit S x) :
    ‖toPareto (x - pFit T x)‖ ^ 2 < zetaTwo * ‖x - qFit S x‖ ^ 2 := by
  have hc : 0 < metricCorrection (x - qFit S x) :=
    lt_of_le_of_ne (metricCorrection_nonneg _) (by
      intro hz
      exact hx (sub_eq_zero.mp ((metricCorrection_eq_zero_iff _).mp hz.symm)))
  linarith [error_lower_identity S T hsame x,
    sq_nonneg ‖toPareto (qFit S x - pFit T x)‖]

/-- Zero error transfers because both closed spaces contain the same functions. -/
theorem exact_fit_iff (x : QHilbert) : x = qFit S x ↔ x = pFit T x := by
  constructor
  · intro h
    have he := p_trial_identity S T hsame x
    have hzero : x - qFit S x = 0 := sub_eq_zero.mpr h
    rw [hzero] at he
    have hz : toPareto (0 : QHilbert) = 0 := toParetoLinear.map_zero
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
    have hr : ‖toPareto (x - pFit T x)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖toPareto (x - pFit T x)‖,
        sq_nonneg ‖toPareto (qFit S x - pFit T x)‖]
    have hn : toPareto (x - pFit T x) = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hr)
    have hq : x - pFit T x = 0 := by
      apply paretoEquiv.injective
      simpa only [paretoEquiv_apply, map_zero] using hn
    exact sub_eq_zero.mp hq
  · intro h
    have he := q_trial_identity S T hsame x
    have hzero : x - pFit T x = 0 := sub_eq_zero.mpr h
    rw [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
    have hr : ‖x - qFit S x‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖x - qFit S x‖, sq_nonneg ‖qFit S x - pFit T x‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hr))

/-- The actual change-of-measure normal equation in weak form. Here reciprocalD
acts on Pareto coordinates, hence multiplies physical value n by 1/n. -/
theorem normal_equation (x : QHilbert) (v : ThresholdHilbert) (hv : v ∈ T) :
    inner ℝ (toPareto (qFit S x - pFit T x)) v +
      inner ℝ (reciprocalD (toPareto (qFit S x - pFit T x))) v =
      inner ℝ (reciprocalD (toPareto (x - pFit T x))) v := by
  have hvq : toQ v ∈ S := (hsame _).mp (by simpa only [toPareto_toQ] using hv)
  have hq : inner ℝ (x - qFit S x) (toQ v) = 0 := by
    rw [real_inner_comm]
    exact (S.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal x)
      _ hvq
  have hp : inner ℝ (toPareto (x - pFit T x)) v = 0 := by
    rw [toPareto_sub, toPareto_pFit, real_inner_comm]
    exact (T.mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal (toPareto x)) _ hv
  have hm := inner_identity (x - qFit S x) (toQ v)
  rw [hq, mul_zero, toPareto_toQ, metricPairing_symmetric] at hm
  unfold metricPairing at hm
  rw [toPareto_toQ] at hm
  rw [← real_inner_comm v (reciprocalD (toPareto (x - qFit S x)))] at hm
  have hd : toPareto (x - qFit S x) =
      toPareto (x - pFit T x) - toPareto (qFit S x - pFit T x) := by
    simp only [toPareto_sub]
    abel
  rw [hd, map_sub, inner_sub_left, inner_sub_left, hp] at hm
  linarith

/-- In Pareto coordinates the displacement solves
`d + P_T(D d) = P_T(D r_P)`. This is an equation, not projection invariance. -/
theorem normal_equation_strong (x : QHilbert) :
    toPareto (qFit S x - pFit T x) +
      T.starProjection (reciprocalD (toPareto (qFit S x - pFit T x))) =
      T.starProjection (reciprocalD (toPareto (x - pFit T x))) := by
  have hd : toPareto (qFit S x - pFit T x) ∈ T := by
    rw [toPareto_sub]
    apply T.sub_mem (toPareto_qFit_mem S T hsame x)
    rw [toPareto_pFit]
    exact T.starProjection_apply_mem _
  have he : T.starProjection
      (reciprocalD (toPareto (x - pFit T x)) -
        reciprocalD (toPareto (qFit S x - pFit T x))) =
      toPareto (qFit S x - pFit T x) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hd
    intro v hv
    rw [inner_sub_left, inner_sub_left]
    linarith [normal_equation S T hsame x v hv]
  rw [map_sub] at he
  calc
    _ = (T.starProjection (reciprocalD (toPareto (x - pFit T x))) -
        T.starProjection (reciprocalD (toPareto (qFit S x - pFit T x)))) +
        T.starProjection (reciprocalD (toPareto (qFit S x - pFit T x))) :=
      congrArg (fun z => z +
        T.starProjection (reciprocalD (toPareto (qFit S x - pFit T x)))) he.symm
    _ = _ := sub_add_cancel _ _

end RiemannResearch.RH.QParetoClosedProjectionComparison
