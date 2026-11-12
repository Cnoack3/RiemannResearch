/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoDisplacementBounds
import RiemannResearch.RH.QParetoMetric
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rescaled inverse series in Pareto coordinates

Source: user-provided Pareto First Projections and Transfer to Q Research Draft,
11 November 2026, Priority 1, uniformly convergent inverse subsection:
https://chatgpt.com/space/page_899f440a0304819182638fe62685b02e.
The compression is rescaled before its Neumann expansion. The exact remainder
and complete norm error are retained at every finite truncation.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QParetoDisplacementResolvent
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QParetoClosedProjectionComparison
open QParetoDisplacementBounds QParetoMetric

theorem reciprocal_norm_sq_le_energy (x : ThresholdHilbert) :
    ‖reciprocalD x‖ ^ 2 ≤ inner ℝ x (reciprocalD x) := by
  rw [hilbert_norm_sq, reciprocalD_inner_tsum]
  apply Summable.tsum_le_tsum _ (hilbert_coordinate_square_summable _)
    (reciprocal_energy_summable x)
  intro n
  rw [reciprocalD_apply, div_pow]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem reflected_reciprocal_norm_le (x : ThresholdHilbert) :
    ‖x - (2 : ℝ) • reciprocalD x‖ ≤ ‖x‖ := by
  have he : ‖x - (2 : ℝ) • reciprocalD x‖ ^ 2 =
      ‖x‖ ^ 2 + 4 * ‖reciprocalD x‖ ^ 2 - 4 * inner ℝ x (reciprocalD x) := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs]
    norm_num
    ring
  nlinarith [reciprocal_norm_sq_le_energy x, norm_nonneg x,
    norm_nonneg (x - (2 : ℝ) • reciprocalD x)]

variable (T : Submodule ℝ ThresholdHilbert) [T.HasOrthogonalProjection]

/-- On T this is (I - 2 T_compressed)/3. -/
def feedback : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (1 / 3 : ℝ) • T.starProjection.comp
    (ContinuousLinearMap.id ℝ ThresholdHilbert - (2 : ℝ) • reciprocalD)

theorem feedback_apply (x : ThresholdHilbert) :
    feedback T x = (1 / 3 : ℝ) • T.starProjection (x - (2 : ℝ) • reciprocalD x) := rfl

theorem feedback_norm_le (x : ThresholdHilbert) :
    ‖feedback T x‖ ≤ (1 / 3 : ℝ) * ‖x‖ := by
  rw [feedback_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
  exact mul_le_mul_of_nonneg_left
    ((T.norm_starProjection_apply_le _).trans (reflected_reciprocal_norm_le x))
    (by norm_num)

def feedbackIter (a : ThresholdHilbert) : ℕ → ThresholdHilbert
  | 0 => a
  | n + 1 => feedback T (feedbackIter a n)

theorem feedbackIter_norm_le (a : ThresholdHilbert) (n : ℕ) :
    ‖feedbackIter T a n‖ ≤ (1 / 3 : ℝ)^n * ‖a‖ := by
  induction n with
  | zero => simp [feedbackIter]
  | succ n ih =>
    exact (feedback_norm_le T _).trans
      ((mul_le_mul_of_nonneg_left ih (by norm_num : 0 ≤ (1/3:ℝ))).trans_eq (by ring))

/-- A finite sum: stage and summation order are explicit. -/
def inverseApprox (a : ThresholdHilbert) (N : ℕ) : ThresholdHilbert :=
  ∑ k ∈ Finset.range N, (2 / 3 : ℝ) • feedbackIter T a k

theorem inverseApprox_succ (a : ThresholdHilbert) (N : ℕ) :
    inverseApprox T a (N + 1) =
      (2 / 3 : ℝ) • a + feedback T (inverseApprox T a N) := by
  simp only [inverseApprox, Finset.sum_range_succ', feedbackIter, map_sum, map_smul]
  abel

theorem centered_normal_equation (d a : ThresholdHilbert) (hd : d ∈ T)
    (he : d + T.starProjection (reciprocalD d) = a) :
    d = (2 / 3 : ℝ) • a + feedback T d := by
  rw [feedback_apply, map_sub, map_smul, Submodule.starProjection_eq_self_iff.mpr hd,
    ← he]
  module

/-- Exact signed finite-remainder recursion. -/
theorem inverseApprox_error_succ (d a : ThresholdHilbert) (hd : d ∈ T)
    (he : d + T.starProjection (reciprocalD d) = a) (N : ℕ) :
    d - inverseApprox T a (N + 1) = feedback T (d - inverseApprox T a N) := by
  rw [inverseApprox_succ, map_sub]
  have hf := centered_normal_equation T d a hd he
  rw [show d - ((2 / 3 : ℝ) • a + feedback T (inverseApprox T a N)) =
    (d - (2 / 3 : ℝ) • a) - feedback T (inverseApprox T a N) by abel]
  have hsub : d - (2 / 3 : ℝ) • a = feedback T d := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using hf
  rw [hsub]

theorem inverseApprox_error_norm (d a : ThresholdHilbert) (hd : d ∈ T)
    (he : d + T.starProjection (reciprocalD d) = a) (N : ℕ) :
    ‖d - inverseApprox T a N‖ ≤ (1 / 3 : ℝ)^N * ‖a‖ := by
  have h : ∀ N, ‖d - inverseApprox T a N‖ ≤ (1 / 3 : ℝ)^N * ‖d‖ := by
    intro N
    induction N with
    | zero => simp [inverseApprox]
    | succ N ih =>
      rw [inverseApprox_error_succ T d a hd he]
      exact (feedback_norm_le T _).trans
        ((mul_le_mul_of_nonneg_left ih (by norm_num : 0 ≤ (1/3:ℝ))).trans_eq (by ring))
  exact (h N).trans (mul_le_mul_of_nonneg_left
    (displacement_le_forcing T d a hd he) (by positivity))

theorem inverseApprox_tendsto (d a : ThresholdHilbert) (hd : d ∈ T)
    (he : d + T.starProjection (reciprocalD d) = a) :
    Tendsto (inverseApprox T a) atTop (𝓝 d) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun N : ℕ => (1 / 3 : ℝ)^N * ‖a‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/3:ℝ))
        (by norm_num : (1/3:ℝ) < 1)).mul_const ‖a‖
  exact squeeze_zero (fun _ => norm_nonneg _) (fun N => by
    rw [norm_sub_rev]
    exact inverseApprox_error_norm T d a hd he N) hlim

/-- The rescaled vector series is absolutely norm summable for every forcing. -/
theorem inverseSeries_summable_norm (a : ThresholdHilbert) :
    Summable (fun k => ‖(2 / 3 : ℝ) • feedbackIter T a k‖) := by
  have hg : Summable (fun k : ℕ => ((2 / 3 : ℝ) * ‖a‖) * (1/3:ℝ)^k) :=
    (hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1/3:ℝ))
      (by norm_num : (1/3:ℝ) < 1)).summable.mul_left _
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hg
  intro k
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
  exact (mul_le_mul_of_nonneg_left (feedbackIter_norm_le T a k)
    (by norm_num : 0 ≤ (2/3:ℝ))).trans_eq (by ring)

/-- The inverse series sums to the unique actual solution of the normal equation. -/
theorem inverseSeries_hasSum (d a : ThresholdHilbert) (hd : d ∈ T)
    (he : d + T.starProjection (reciprocalD d) = a) :
    HasSum (fun k => (2 / 3 : ℝ) • feedbackIter T a k) d := by
  apply ((inverseSeries_summable_norm T a).of_norm.hasSum_iff_tendsto_nat).mpr
  exact inverseApprox_tendsto T d a hd he

/-- The inverse is constructed by the absolutely convergent, rescaled series. -/
def inverseSum (a : ThresholdHilbert) : ThresholdHilbert :=
  ∑' k, (2 / 3 : ℝ) • feedbackIter T a k

theorem inverseApprox_tendsto_sum (a : ThresholdHilbert) :
    Tendsto (inverseApprox T a) atTop (𝓝 (inverseSum T a)) :=
  (inverseSeries_summable_norm T a).of_norm.hasSum.tendsto_sum_nat

private theorem inverseApprox_mem (a : ThresholdHilbert) (ha : a ∈ T) (N : ℕ) :
    inverseApprox T a N ∈ T := by
  induction N with
  | zero => simp [inverseApprox]
  | succ N ih =>
    rw [inverseApprox_succ, feedback_apply]
    exact T.add_mem (T.smul_mem _ ha) (T.smul_mem _ (T.starProjection_apply_mem _))

theorem inverseSum_mem (a : ThresholdHilbert) (ha : a ∈ T) : inverseSum T a ∈ T := by
  have ht := inverseApprox_tendsto_sum T a
  have hp := (T.starProjection.continuous.tendsto (inverseSum T a)).comp ht
  have hp' : Tendsto (inverseApprox T a) atTop
      (𝓝 (T.starProjection (inverseSum T a))) := by
    simpa only [Function.comp_def,
      Submodule.starProjection_eq_self_iff.mpr (inverseApprox_mem T a ha _)] using hp
  apply Submodule.starProjection_eq_self_iff.mp
  exact tendsto_nhds_unique hp' ht

theorem inverseSum_normal_equation (a : ThresholdHilbert) (ha : a ∈ T) :
    inverseSum T a + T.starProjection (reciprocalD (inverseSum T a)) = a := by
  have ht := inverseApprox_tendsto_sum T a
  have hs := ht.comp (tendsto_add_atTop_nat 1)
  have hf : Tendsto (fun N => (2 / 3 : ℝ) • a + feedback T (inverseApprox T a N))
      atTop (𝓝 ((2 / 3 : ℝ) • a + feedback T (inverseSum T a))) :=
    tendsto_const_nhds.add ((feedback T).continuous.tendsto (inverseSum T a) |>.comp ht)
  have hs' : Tendsto (fun N => (2 / 3 : ℝ) • a + feedback T (inverseApprox T a N))
      atTop (𝓝 (inverseSum T a)) := by
    simpa only [Function.comp_def, inverseApprox_succ] using hs
  have he : inverseSum T a = (2 / 3 : ℝ) • a + feedback T (inverseSum T a) :=
    tendsto_nhds_unique hs' hf
  rw [feedback_apply, map_sub, map_smul,
    Submodule.starProjection_eq_self_iff.mpr (inverseSum_mem T a ha)] at he
  have hz : (3 / 2 : ℝ) • (inverseSum T a -
      ((2 / 3 : ℝ) • a + (1 / 3 : ℝ) •
        (inverseSum T a - (2 : ℝ) • T.starProjection (reciprocalD (inverseSum T a))))) = 0 := by
    rw [← he, sub_self, smul_zero]
  have hid : (3 / 2 : ℝ) • (inverseSum T a -
      ((2 / 3 : ℝ) • a + (1 / 3 : ℝ) •
        (inverseSum T a - (2 : ℝ) • T.starProjection (reciprocalD (inverseSum T a))))) =
      inverseSum T a + T.starProjection (reciprocalD (inverseSum T a)) - a := by module
  rw [hid] at hz
  exact sub_eq_zero.mp hz

theorem inverseSum_norm_bounds (a : ThresholdHilbert) (ha : a ∈ T) :
    ‖a‖ / 2 ≤ ‖inverseSum T a‖ ∧ ‖inverseSum T a‖ ≤ ‖a‖ := by
  have he := inverseSum_normal_equation T a ha
  constructor
  · linarith [forcing_le_twice_displacement T (inverseSum T a) a he]
  · exact displacement_le_forcing T _ _ (inverseSum_mem T a ha) he

/-- Every forcing in the closed subspace has a unique solution; no arithmetic premise. -/
theorem existsUnique_normal_solution (a : ThresholdHilbert) (ha : a ∈ T) :
    ∃! d : ThresholdHilbert, d ∈ T ∧ d + T.starProjection (reciprocalD d) = a := by
  refine ⟨inverseSum T a, ⟨inverseSum_mem T a ha, inverseSum_normal_equation T a ha⟩, ?_⟩
  intro d hd
  exact normal_solution_unique T d (inverseSum T a) a hd.1 (inverseSum_mem T a ha)
    hd.2 (inverseSum_normal_equation T a ha)

/-- The inverse is applied to the actual canonical forcing of the two physical fits. -/
theorem matched_displacement_eq_inverseSum
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (hsame : ∀ f : QHilbert, toPareto f ∈ T ↔ f ∈ S) (x : QHilbert) :
    toPareto (qFit S x - pFit T x) =
      inverseSum T (T.starProjection (reciprocalD (toPareto (x - pFit T x)))) := by
  have hd : toPareto (qFit S x - pFit T x) ∈ T := by
    rw [toPareto_sub, toPareto_pFit]
    exact T.sub_mem (toPareto_qFit_mem S T hsame x) (T.starProjection_apply_mem _)
  exact normal_solution_unique T _ _ _ hd
    (inverseSum_mem T _ (T.starProjection_apply_mem _))
    (normal_equation_strong S T hsame x)
    (inverseSum_normal_equation T _ (T.starProjection_apply_mem _))

/-- A fully instantiated geometric error bound for every matched finite or closed space. -/
theorem matched_inverseApprox_error
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (hsame : ∀ f : QHilbert, toPareto f ∈ T ↔ f ∈ S) (x : QHilbert) (N : ℕ) :
    ‖toPareto (qFit S x - pFit T x) -
      inverseApprox T (T.starProjection (reciprocalD (toPareto (x - pFit T x)))) N‖ ≤
        (1 / 3 : ℝ)^N * ‖T.starProjection (reciprocalD (toPareto (x - pFit T x)))‖ := by
  rw [matched_displacement_eq_inverseSum T S hsame x]
  exact inverseApprox_error_norm T _ _
    (inverseSum_mem T _ (T.starProjection_apply_mem _))
    (inverseSum_normal_equation T _ (T.starProjection_apply_mem _)) N

end RiemannResearch.RH.QParetoDisplacementResolvent
