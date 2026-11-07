/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoSquareRootEnergy
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Compact square-root correction and bounded coordinate limits

Source: CrossedDistanceLeanHandoff20261106.md, Priority 2, for the proposed
compactness and weaker convergence route. The proof uses finite coordinate
restrictions and retains the complete infinite remainder. Mathlib supplies
the closure of compact operators under operator-norm limits.

The limit is rootDefect f, not zero. No legal-space membership is inferred.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QFiniteSupportDualCriterion
open ZetaTwoHilbert

/-- Orthogonal restriction to the first N encoded coordinates as a continuous linear map. -/
def finiteHeadCLM (N : ℕ) : QHilbert →L[ℝ] QHilbert :=
  ∑ n ∈ Finset.range N,
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 n).comp
      (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n)

theorem finiteHeadCLM_apply (N : ℕ) (f : QHilbert) :
    finiteHeadCLM N f = finiteHead N f := by
  simp only [finiteHeadCLM, sum_apply,
    ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]
  rfl

theorem finiteHeadCLM_compact (N : ℕ) : IsCompactOperator (finiteHeadCLM N) := by
  induction N with
  | zero =>
    simpa [finiteHeadCLM] using
      (isCompactOperator_zero : IsCompactOperator (0 : QHilbert → QHilbert))
  | succ N ih =>
    have hsingle := (isCompactOperator_of_locallyCompactSpace_rng
      (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 N)).comp_clm
        (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 N)
    simpa [finiteHeadCLM, Finset.sum_range_succ, ContinuousLinearMap.coe_comp] using ih.add hsingle

theorem finiteHead_remainder_norm_le (N : ℕ) (f : QHilbert) :
    ‖f - finiteHead N f‖ ≤ ‖f‖ := by
  nlinarith [finiteHead_norm_sq_split N f, sq_nonneg ‖finiteHead N f‖,
    norm_nonneg f, norm_nonneg (f - finiteHead N f)]

theorem finiteHead_tendsto_of_coordinates {G : ℕ → QHilbert} {f : QHilbert}
    (hG : ∀ n, Tendsto (fun M => G M n) atTop (𝓝 (f n))) (N : ℕ) :
    Tendsto (fun M => finiteHead N (G M - f)) atTop (𝓝 0) := by
  induction N with
  | zero => simp [finiteHead]
  | succ N ih =>
    have hc : Tendsto (fun M => (G M - f) N) atTop (𝓝 (0 : ℝ)) := by
      change Tendsto (fun M => G M N - f N) atTop (𝓝 (0 : ℝ))
      simpa only [sub_self] using (hG N).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => f N) atTop (𝓝 (f N)))
    have hn : Tendsto (fun M => lp.single 2 N ((G M - f) N) : ℕ → QHilbert)
        atTop (𝓝 0) := by
      have h := ((lp.isometry_single (E := fun _ : ℕ => ℝ) (p := 2) N).continuous.tendsto 0).comp hc
      simpa only [lp.single_zero, Function.comp_def] using h
    simpa only [finiteHead, Finset.sum_range_succ, add_zero] using ih.add hn

end RiemannResearch.RH.QFiniteSupportDualCriterion

namespace RiemannResearch.RH.QParetoIsometricTransport
open ZetaTwoHilbert QFiniteSupportDualCriterion

/-- Finite-rank approximation of the complete square-root correction. -/
def rootDefectHead (N : ℕ) : QHilbert →L[ℝ] QHilbert :=
  rootDefect.comp (finiteHeadCLM N)

theorem rootDefectHead_compact (N : ℕ) : IsCompactOperator (rootDefectHead N) :=
  (finiteHeadCLM_compact N).clm_comp rootDefect

/-- Every coordinate beyond the finite head is retained in the error. -/
theorem rootDefectHead_error (N : ℕ) (f : QHilbert) :
    ‖rootDefect f - rootDefectHead N f‖ ≤ ‖f‖ / (2 * (N : ℝ)+3) := by
  change ‖rootDefect f - rootDefect (finiteHeadCLM N f)‖ ≤ _
  rw [finiteHeadCLM_apply, ← map_sub]
  have hh : ∀ n < N, (f - finiteHead N f) n = 0 := by
    intro n hn
    change f n - finiteHead N f n = 0
    rw [finiteHead_apply_of_lt N f n hn, sub_self]
  exact (rootDefect_norm_le_of_head_zero _ N hh).trans
    (div_le_div_of_nonneg_right (finiteHead_remainder_norm_le N f) (by positivity))

theorem rootDefectHead_opNorm_error (N : ℕ) :
    ‖rootDefect - rootDefectHead N‖ ≤ 1 / (2 * (N : ℝ)+3) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro f
  simpa only [sub_apply, one_div_mul_eq_div] using
    rootDefectHead_error N f

theorem rootDefectHead_tendsto :
    Tendsto rootDefectHead atTop (𝓝 rootDefect) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [dist_eq_norm, norm_sub_rev]
  apply (rootDefectHead_opNorm_error n).trans_lt
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ)+3)).mpr
  have hh : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- Compactness follows from the finite-rank approximation in operator norm. -/
theorem rootDefect_compact : IsCompactOperator rootDefect :=
  isCompactOperator_of_tendsto rootDefectHead_tendsto
    (Eventually.of_forall rootDefectHead_compact)

/-- Bounded coordinatewise convergence becomes strong convergence after applying J. -/
theorem rootDefect_tendsto_of_bounded_coordinates {G : ℕ → QHilbert} {f : QHilbert}
    (C : ℝ) (hbound : ∀ M, ‖G M‖ ≤ C)
    (hG : ∀ n, Tendsto (fun M => G M n) atTop (𝓝 (f n))) :
    Tendsto (fun M => rootDefect (G M)) atTop (𝓝 (rootDefect f)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((C + ‖f‖) / (ε / 2))
  have htail : (C + ‖f‖) / (2 * (N : ℝ)+3) < ε/2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ)+3)).mpr
    have hh : C + ‖f‖ < (N : ℝ) * (ε/2) :=
      (div_lt_iff₀ (half_pos hε)).mp hN
    nlinarith
  have hhead : Tendsto (fun M => ‖rootDefect (finiteHead N (G M-f))‖)
      atTop (𝓝 0) := by
    simpa only [map_zero, norm_zero, Function.comp_def] using
      ((rootDefect.continuous.tendsto 0).comp
        (finiteHead_tendsto_of_coordinates hG N)).norm
  have hev := (tendsto_order.1 hhead).2 (ε/2) (half_pos hε)
  filter_upwards [hev] with M hM
  rw [dist_eq_norm, ← map_sub]
  have he := rootDefect_head_trial_bound (G M-f) (finiteHead N (G M-f)) 0 N
    (fun n hn => (finiteHead_apply_of_lt N (G M-f) n hn).symm)
  simp only [sub_zero] at he
  have hr : ‖(G M-f) - finiteHead N (G M-f)‖ ≤ C + ‖f‖ :=
    (finiteHead_remainder_norm_le N (G M-f)).trans
      ((norm_sub_le (G M) f).trans (add_le_add (hbound M) le_rfl))
  have hd := div_le_div_of_nonneg_right hr
    (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ)+3)
  linarith

/-- In particular, bounded convergence of all Hilbert-space pairings suffices. -/
theorem rootDefect_tendsto_of_bounded_weak {G : ℕ → QHilbert} {f : QHilbert}
    (C : ℝ) (hbound : ∀ M, ‖G M‖ ≤ C)
    (hweak : ∀ v : QHilbert,
      Tendsto (fun M => inner ℝ (G M) v) atTop (𝓝 (inner ℝ f v))) :
    Tendsto (fun M => rootDefect (G M)) atTop (𝓝 (rootDefect f)) := by
  apply rootDefect_tendsto_of_bounded_coordinates C hbound
  intro n
  simpa only [lp.inner_single_right, RCLike.inner_apply, conj_trivial, one_mul] using
    hweak (lp.single 2 n (1 : ℝ))

/-- The correction of a coordinate head is still a coordinate head. -/
theorem rootDefect_finiteHead (M : ℕ) (f : QHilbert) :
    rootDefect (finiteHead M f) = finiteHead M (rootDefect f) := by
  apply lp.ext
  funext n
  by_cases hn : n < M
  · rw [rootDefect_apply, finiteHead_apply_of_lt M f n hn,
      finiteHead_apply_of_lt M (rootDefect f) n hn, rootDefect_apply]
  · rw [rootDefect_apply, finiteHead_apply_eq_zero M f n (Nat.le_of_not_gt hn),
      finiteHead_apply_eq_zero M (rootDefect f) n (Nat.le_of_not_gt hn), mul_zero]

/-- Finite target pairings do not replace the complete Gram matrix. -/
theorem inner_rootDefect_finiteHead (x f : QHilbert) (M : ℕ) :
    inner ℝ x (rootDefect (finiteHead M f)) =
      ∑ n ∈ Finset.range M,
        ((1 - Real.sqrt (((n : ℝ) + 1) / ((n : ℝ) + 2))) * f n) * x n := by
  rw [rootDefect_finiteHead, inner_finiteHead_eq_sum]
  simp only [rootDefect_apply]

end RiemannResearch.RH.QParetoIsometricTransport
