/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoClosedProjectionComparison
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pareto displacement: complete energy and stable forcing bounds

Source: user-provided Pareto First Projections and Transfer to Q Research Draft,
11 November 2026, Priority 1 and the stable inversion section:
https://chatgpt.com/space/page_899f440a0304819182638fe62685b02e.
The source supplies the statements. The exact positive-remainder proof below
strengthens its sharp displacement inequality. No density premise is used.
-/

noncomputable section
namespace RiemannResearch.RH.QParetoDisplacementBounds
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QParetoClosedProjectionComparison

theorem reciprocal_energy_le (x : ThresholdHilbert) :
    inner ℝ x (reciprocalD x) ≤ ‖x‖ ^ 2 := by
  have h := (real_inner_le_norm x (reciprocalD x)).trans
    (mul_le_mul_of_nonneg_left (reciprocalD_norm_le x) (norm_nonneg x))
  nlinarith only [h]

/-- Exact identity retaining both nonnegative remainder terms. -/
theorem sharp_energy_remainder (r d : ThresholdHilbert)
    (horth : inner ℝ r d = 0)
    (hnormal : inner ℝ d (reciprocalD r) =
      ‖d‖ ^ 2 + inner ℝ d (reciprocalD d)) :
    ‖r‖ ^ 2 = 8 * ‖d‖ ^ 2 +
      inner ℝ (r - (4 : ℝ) • d) (reciprocalD (r - (4 : ℝ) • d)) +
      (‖r + (2 : ℝ) • d‖ ^ 2 -
        inner ℝ (r + (2 : ℝ) • d) (reciprocalD (r + (2 : ℝ) • d))) := by
  have hsym : inner ℝ r (reciprocalD d) = inner ℝ d (reciprocalD r) := by
    rw [← reciprocalD_symmetric, real_inner_comm]
  simp only [map_sub, map_add, map_smul, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    norm_add_sq_real, norm_smul, Real.norm_eq_abs, horth, hsym, hnormal]
  norm_num
  ring

theorem sharp_energy_bound (r d : ThresholdHilbert)
    (horth : inner ℝ r d = 0)
    (hnormal : inner ℝ d (reciprocalD r) =
      ‖d‖ ^ 2 + inner ℝ d (reciprocalD d)) :
    8 * ‖d‖ ^ 2 ≤ ‖r‖ ^ 2 := by
  linarith [sharp_energy_remainder r d horth hnormal,
    reciprocalD_positive (r - (4 : ℝ) • d),
    reciprocal_energy_le (r + (2 : ℝ) • d)]

theorem sharp_norm_bound (r d : ThresholdHilbert)
    (horth : inner ℝ r d = 0)
    (hnormal : inner ℝ d (reciprocalD r) =
      ‖d‖ ^ 2 + inner ℝ d (reciprocalD d)) :
    ‖d‖ ≤ ‖r‖ / (2 * Real.sqrt 2) := by
  have hs := sharp_energy_bound r d horth hnormal
  have hroot : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrootpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt 2)).mpr
  have hn : 0 ≤ ‖d‖ * (2 * Real.sqrt 2) := by positivity
  nlinarith [norm_nonneg r, sq_nonneg (‖r‖ - ‖d‖ * (2 * Real.sqrt 2))]

variable (T : Submodule ℝ ThresholdHilbert) [T.HasOrthogonalProjection]

private theorem inner_projection_right (d x : ThresholdHilbert) (hd : d ∈ T) :
    inner ℝ d (T.starProjection x) = inner ℝ d x := by
  have h := Submodule.inner_right_of_mem_orthogonal hd
    (Submodule.sub_starProjection_mem_orthogonal (K := T) x)
  rw [inner_sub_right] at h
  linarith only [h]

/-- The complete forcing controls displacement with inverse norm at most one. -/
theorem displacement_le_forcing (d a : ThresholdHilbert) (hd : d ∈ T)
    (he : d + T.starProjection (reciprocalD d) = a) : ‖d‖ ≤ ‖a‖ := by
  have hn := congrArg (fun x => inner ℝ d x) he
  rw [inner_add_right, real_inner_self_eq_norm_sq,
    inner_projection_right T d _ hd] at hn
  have hcs := real_inner_le_norm d a
  have hpos := reciprocalD_positive d
  by_cases hz : ‖d‖ = 0
  · simpa only [hz] using norm_nonneg a
  · have hdpos : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg d) (Ne.symm hz)
    nlinarith

/-- The lower estimate keeps the same complete forcing; no coefficient norm occurs. -/
theorem forcing_le_twice_displacement (d a : ThresholdHilbert)
    (he : d + T.starProjection (reciprocalD d) = a) : ‖a‖ ≤ 2 * ‖d‖ := by
  rw [← he]
  have hp := (T.norm_starProjection_apply_le (reciprocalD d)).trans (reciprocalD_norm_le d)
  linarith [norm_add_le d (T.starProjection (reciprocalD d))]

theorem normal_solution_unique (d e a : ThresholdHilbert) (hd : d ∈ T) (he : e ∈ T)
    (hde : d + T.starProjection (reciprocalD d) = a)
    (hee : e + T.starProjection (reciprocalD e) = a) : d = e := by
  have hzero : (d - e) + T.starProjection (reciprocalD (d - e)) = 0 := by
    rw [map_sub, map_sub]
    rw [show d - e + (T.starProjection (reciprocalD d) -
      T.starProjection (reciprocalD e)) =
        (d + T.starProjection (reciprocalD d)) -
          (e + T.starProjection (reciprocalD e)) by abel]
    rw [hde, hee, sub_self]
  have hn := displacement_le_forcing T (d - e) 0 (T.sub_mem hd he) hzero
  simpa only [norm_zero, norm_le_zero_iff, sub_eq_zero] using hn

variable (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
variable (hsame : ∀ f : QHilbert, toPareto f ∈ T ↔ f ∈ S)
include hsame

/-- The actual two physical projections satisfy the sharp bound for every target. -/
theorem matched_sharp_energy_bound (x : QHilbert) :
    8 * ‖toPareto (qFit S x - pFit T x)‖ ^ 2 ≤
      ‖toPareto (x - pFit T x)‖ ^ 2 := by
  let d := toPareto (qFit S x - pFit T x)
  let r := toPareto (x - pFit T x)
  have hd : d ∈ T := by
    dsimp only [d]
    rw [toPareto_sub, toPareto_pFit]
    exact T.sub_mem (toPareto_qFit_mem S T hsame x) (T.starProjection_apply_mem _)
  have horth : inner ℝ r d = 0 := by
    rw [real_inner_comm]
    apply Submodule.inner_right_of_mem_orthogonal hd
    dsimp only [r]
    rw [toPareto_sub, toPareto_pFit]
    exact Submodule.sub_starProjection_mem_orthogonal _
  have he := normal_equation S T hsame x d hd
  change inner ℝ d d + inner ℝ (reciprocalD d) d = inner ℝ (reciprocalD r) d at he
  have hn : inner ℝ d (reciprocalD r) =
      ‖d‖ ^ 2 + inner ℝ d (reciprocalD d) := by
    rw [real_inner_self_eq_norm_sq, ← real_inner_comm (reciprocalD d) d,
      ← real_inner_comm (reciprocalD r) d] at he
    exact he.symm
  exact sharp_energy_bound r d horth hn

end RiemannResearch.RH.QParetoDisplacementBounds
