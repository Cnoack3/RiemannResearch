/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullWeakHeadCorrections
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QFullHeadRepair
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFullCofinalHarmonic
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.Analysis.DenseProjectionTesting
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Finite dual witnesses obstruct bounded legal interpolation

Source: the user's request to exploit weak-star compactness toward RH,
6 November 2026, continued from CrossedDistanceLeanHandoff20261106.md.
The finite-test criterion and exact finite-head repair machinery are reused.
These estimates give a quantitative dual form of the compactness obstruction:
if a target is outside the closed legal span, every family matching increasing
heads has norm tending to infinity. Uniformly bounded interpolation of the
specific target B(displacement) is an explicit Open RH provider.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QFullHeadObstruction
open ZetaTwoHilbert QFullResidueProjection QFullDisplacement QShiftedReciprocal
open QFiniteSupportDualCriterion QFullHeadRepair
open RiemannResearch.Analysis.DenseProjectionTesting

/-- Exact head agreement gives a full-norm dual lower bound for a legal interpolant. -/
theorem finite_test_bound_of_matching_head (M : ℕ) (x y a : QHilbert)
    (hy : y ∈ closure) (hh : ∀ n < M, y n = x n) :
    |inner ℝ x (finiteHead M a)| ≤
      ‖y‖ * ‖closure.starProjection (finiteHead M a)‖ := by
  have he : inner ℝ y (finiteHead M a) = inner ℝ x (finiteHead M a) := by
    rw [inner_finiteHead_eq_sum, inner_finiteHead_eq_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hh n (Finset.mem_range.mp hn)]
  rw [← he, inner_eq_projected_test closure hy (finiteHead M a)]
  exact abs_real_inner_le_norm _ _

/-- A single finite dual witness eventually rules out every prescribed norm bound. -/
theorem exists_finite_head_norm_obstruction (x : QHilbert) (hx : x ∉ closure) (C : ℝ) :
    ∃ M : ℕ, ∃ a : QHilbert,
      C * ‖closure.starProjection (finiteHead M a)‖ < |inner ℝ x (finiteHead M a)| ∧
      ∀ y : QHilbert, y ∈ closure → (∀ n < M, y n = x n) → C < ‖y‖ := by
  classical
  have hb : ¬ ∀ M a, |inner ℝ x (finiteHead M a)| ≤
      C * ‖closure.starProjection (finiteHead M a)‖ := by
    intro h
    exact hx ((mem_closure_iff_finite_test_bound x).mpr ⟨C, h⟩)
  obtain ⟨M, hM⟩ := not_forall.mp hb
  obtain ⟨a, ha⟩ := not_forall.mp hM
  have hlt := lt_of_not_ge ha
  refine ⟨M, a, hlt, ?_⟩
  intro y hy hh
  have he := finite_test_bound_of_matching_head M x y a hy hh
  by_contra hn
  have hn' : ‖y‖ ≤ C := le_of_not_gt hn
  exact (not_le_of_gt hlt) (he.trans
    (mul_le_mul_of_nonneg_right hn' (norm_nonneg _)))

/-- Divergence holds for every increasing-head interpolation family, not only a subsequence. -/
theorem exact_head_norm_tendsto_atTop (x : QHilbert) (hx : x ∉ closure)
    {F : ℕ → QHilbert} (hF : ∀ N, F N ∈ closure)
    (hhead : ∀ N n, n < N → F N n = x n) :
    Tendsto (fun N => ‖F N‖) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  obtain ⟨M, a, ha, hM⟩ := exists_finite_head_norm_obstruction x hx C
  exact (eventually_ge_atTop M).mono fun N hMN =>
    (hM (F N) (hF N) (fun n hn => hhead N n (lt_of_lt_of_le hn hMN))).le

/-- Every target in the closure admits bounded finite legal interpolants on all heads. -/
theorem bounded_exact_head_interpolants_of_mem (x : QHilbert) (hx : x ∈ closure) :
    ∀ M : ℕ, ∃ y : QHilbert, y ∈ legalSpan ∧
      (∀ n < M, y n = x n) ∧ ‖y‖ ≤ ‖x‖ + 1 := by
  intro M
  obtain ⟨y, hy, hh, hn⟩ := exists_exact_head_norm_sq_lt M x hx 1 (by norm_num)
  refine ⟨y, hy, hh, ?_⟩
  apply (sq_le_sq₀ (norm_nonneg y) (by positivity : 0 ≤ ‖x‖ + 1)).mp
  calc
    ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 + 1 := hn.le
    _ ≤ (‖x‖ + 1) ^ 2 := by nlinarith [norm_nonneg x]

/-- Bounded exact-head interpolation is precisely closed-span membership.
The reverse implication uses Banach--Alaoglu through the bounded finite-test theorem. -/
theorem mem_closure_iff_bounded_exact_heads (x : QHilbert) :
    x ∈ closure ↔ ∃ C : ℝ, ∀ M : ℕ, ∃ y : QHilbert,
      y ∈ legalSpan ∧ (∀ n < M, y n = x n) ∧ ‖y‖ ≤ C := by
  constructor
  · intro hx
    exact ⟨‖x‖ + 1, bounded_exact_head_interpolants_of_mem x hx⟩
  · rintro ⟨C, hC⟩
    have hfinite : ∀ N, ∃ y ∈ closure, ‖y‖ ≤ C ∧
        ∀ n < N, (ContinuousLinearMap.id ℝ QHilbert) y n = x n := by
      intro N
      obtain ⟨y, hy, hh, hn⟩ := hC N
      exact ⟨y, legalSpan.le_topologicalClosure hy, hn, hh⟩
    obtain ⟨y, hy, _hn, he⟩ :=
      (closure.bounded_lp_head_image_feasibility_iff C
        (ContinuousLinearMap.id ℝ QHilbert) x).mp hfinite
    change y = x at he
    rwa [← he]

/-- One target-specific bounded family is enough; no global operator invariance is assumed. -/
theorem displacement_eq_zero_iff_bounded_reciprocal_heads :
    displacement = 0 ↔ ∃ C : ℝ, ∀ M : ℕ, ∃ y : QHilbert,
      y ∈ legalSpan ∧ (∀ n < M, y n = B displacement n) ∧ ‖y‖ ≤ C :=
  displacement_eq_zero_iff_reciprocal_mem.trans
    (mem_closure_iff_bounded_exact_heads (B displacement))

/-- A nonzero actual displacement forces every reciprocal-head repair family to diverge. -/
theorem reciprocal_head_norm_tendsto_atTop (hd : displacement ≠ 0)
    {F : ℕ → QHilbert} (hF : ∀ N, F N ∈ closure)
    (hhead : ∀ N n, n < N → F N n = B displacement n) :
    Tendsto (fun N => ‖F N‖) atTop atTop := by
  have hx : B displacement ∉ closure := fun h =>
    hd (displacement_eq_zero_iff_reciprocal_mem.mpr h)
  exact exact_head_norm_tendsto_atTop (B displacement) hx hF hhead

/-- Conditional research reduction. A uniform full-norm bound is still required. -/
theorem riemannHypothesis_of_bounded_reciprocal_heads
    (h : ∃ C : ℝ, ∀ M : ℕ, ∃ y : QHilbert,
      y ∈ legalSpan ∧ (∀ n < M, y n = B displacement n) ∧ ‖y‖ ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_displacement_eq_zero
    (displacement_eq_zero_iff_bounded_reciprocal_heads.mpr h)

end RiemannResearch.RH.QFullHeadObstruction
