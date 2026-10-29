/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QProjectionMoments
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# An actual-residual lower bound for every legal exact-head approximant

Source: the user's symbolic CRT epsilon weak-matrix audit, 29 October 2026.
The residual is the actual squarefree projection residual. The pairing identity
retains its complete infinite tail and applies to every legal exact-head vector,
independently of the period, coefficient choice, or optimization procedure.

If this residual is nonzero, every cofinal exact-head family has complete error
norm tending to infinity. This is a conditional obstruction, not an assertion
that the residual is nonzero or zero. No RH hypothesis or density provider is
used or established.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeExactHeadResidualBarrier
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QFiniteSupportDualCriterion QAnnihilatorTailEscape QSquarefreeResidualTail

theorem legal_mem_optimizer_closure (F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan) :
    F ∈ ZetaTwoOptimizerStage.closure := by
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact qSquarefreeCRTSpan.le_topologicalClosure hF

/-- Exact signed identity for every legal vector matching the physical head. -/
theorem exact_head_residual_tail_identity (H : ℕ) (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence F k = 1) :
    ‖limitingResidual‖ ^ 2 =
      inner ℝ (limitingResidual - finiteHead H limitingResidual) (qOne - F) := by
  have ho : inner ℝ limitingResidual F = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal
      (legal_mem_optimizer_closure F hF) limitingResidual_mem_squarefree_orthogonal
  have hm : inner ℝ limitingResidual (qOne - F) = ‖limitingResidual‖ ^ 2 := by
    rw [inner_sub_right, ho, sub_zero]
    exact qResidual_inner_qOne ZetaTwoOptimizerStage.closure
  have hmatch : inner ℝ F (finiteHead H limitingResidual) =
      inner ℝ qOne (finiteHead H limitingResidual) := by
    apply inner_finiteHead_eq_of_matching_head
    intro k hk hkH
    rw [hh k hk hkH, qSequence_qOne]
    simp [qOneSequence, Nat.ne_of_gt hk]
  have hhead : inner ℝ (finiteHead H limitingResidual) (qOne - F) = 0 := by
    rw [real_inner_comm, inner_sub_left, hmatch, sub_self]
  rw [inner_sub_left, hhead, sub_zero, hm]

theorem residual_sq_le_tail_mul_error (H : ℕ) (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence F k = 1) :
    ‖limitingResidual‖ ^ 2 ≤ ‖tail H limitingResidual‖ * ‖qOne - F‖ := by
  have hi : inner ℝ (tail H limitingResidual) (qOne - F) =
      ‖limitingResidual‖ ^ 2 := (exact_head_residual_tail_identity H F hF hh).symm
  have h := abs_real_inner_le_norm (tail H limitingResidual) (qOne - F)
  rw [hi, abs_of_nonneg (sq_nonneg _)] at h
  exact h

/-- Cauchy--Schwarz preserves the entire tail and complete error norm. -/
theorem residual_fourth_le_tail_sq_mul_error_sq (H : ℕ) (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence F k = 1) :
    ‖limitingResidual‖ ^ 4 ≤ ‖tail H limitingResidual‖ ^ 2 * ‖qOne - F‖ ^ 2 := by
  have h := residual_sq_le_tail_mul_error H F hF hh
  have hs := mul_self_le_mul_self (sq_nonneg ‖limitingResidual‖) h
  nlinarith

theorem residual_tail_norm_pos (hr : limitingResidual ≠ 0) (H : ℕ) (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence F k = 1) :
    0 < ‖tail H limitingResidual‖ := by
  have hc : 0 < ‖limitingResidual‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hr)
  have h := residual_sq_le_tail_mul_error H F hF hh
  by_contra ht
  have hz : ‖tail H limitingResidual‖ = 0 :=
    le_antisymm (le_of_not_gt ht) (norm_nonneg _)
  rw [hz, zero_mul] at h
  linarith

/-- A positive residual supplies a quantitative lower bound for every witness. -/
theorem error_norm_lower_bound (hr : limitingResidual ≠ 0) (H : ℕ) (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence F k = 1) :
    ‖limitingResidual‖ ^ 2 / ‖tail H limitingResidual‖ ≤ ‖qOne - F‖ := by
  apply (div_le_iff₀ (residual_tail_norm_pos hr H F hF hh)).mpr
  simpa only [mul_comm] using residual_sq_le_tail_mul_error H F hF hh

theorem error_sq_lower_bound (hr : limitingResidual ≠ 0) (H : ℕ) (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence F k = 1) :
    ‖limitingResidual‖ ^ 4 / ‖tail H limitingResidual‖ ^ 2 ≤ ‖qOne - F‖ ^ 2 := by
  apply (div_le_iff₀ (sq_pos_of_pos (residual_tail_norm_pos hr H F hF hh))).mpr
  simpa only [mul_comm] using residual_fourth_le_tail_sq_mul_error_sq H F hF hh

/-- Exact constrained completion with a signed, nonnegative remainder.
This lower bound is independent of the period and of the chosen dictionary. -/
theorem exact_head_residual_completion (H : ℕ) (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence F k = 1)
    (ht : ‖tail H limitingResidual‖ ^ 2 ≠ 0) :
    let h := finiteHead H qOne
    let t := tail H limitingResidual
    let a := inner ℝ limitingResidual h
    ‖F‖ ^ 2 = ‖h‖ ^ 2 + a ^ 2 / ‖t‖ ^ 2 +
      ‖F - h + (a / ‖t‖ ^ 2) • t‖ ^ 2 := by
  dsimp only
  have hmatch (u : QHilbert) : inner ℝ F (finiteHead H u) =
      inner ℝ qOne (finiteHead H u) := by
    apply inner_finiteHead_eq_of_matching_head
    intro k hk hkH
    rw [hh k hk hkH, qSequence_qOne]
    simp [qOneSequence, Nat.ne_of_gt hk]
  have hhead : inner ℝ F (finiteHead H qOne) = ‖finiteHead H qOne‖ ^ 2 := by
    rw [hmatch]
    have hi := finiteHead_inner H qOne (finiteHead H qOne)
    rw [finiteHead_idem, real_inner_self_eq_norm_sq] at hi
    exact hi.symm
  have hsplit : ‖F‖ ^ 2 = ‖finiteHead H qOne‖ ^ 2 + ‖F - finiteHead H qOne‖ ^ 2 := by
    rw [norm_sub_sq_real, hhead]
    ring
  have ho : inner ℝ limitingResidual F = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal
      (legal_mem_optimizer_closure F hF) limitingResidual_mem_squarefree_orthogonal
  have hp : inner ℝ (finiteHead H limitingResidual) (F - finiteHead H qOne) = 0 := by
    rw [real_inner_comm, inner_sub_left, hmatch, finiteHead_inner, finiteHead_idem, sub_self]
  have hpair : inner ℝ (F - finiteHead H qOne) (tail H limitingResidual) =
      -inner ℝ limitingResidual (finiteHead H qOne) := by
    rw [real_inner_comm, tail, inner_sub_left, hp, sub_zero, inner_sub_right, ho, zero_sub]
  have hshift :
      ‖F - finiteHead H qOne +
        (inner ℝ limitingResidual (finiteHead H qOne) / ‖tail H limitingResidual‖ ^ 2) •
          tail H limitingResidual‖ ^ 2 =
      ‖F - finiteHead H qOne‖ ^ 2 -
        (inner ℝ limitingResidual (finiteHead H qOne)) ^ 2 / ‖tail H limitingResidual‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right, hpair]
    have htnorm : ‖tail H limitingResidual‖ ≠ 0 := by
      intro hz
      apply ht
      rw [hz]
      norm_num
    field_simp [ht, htnorm]
    ring
  linarith

theorem exact_head_energy_lower_bound (H : ℕ) (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence F k = 1)
    (ht : ‖tail H limitingResidual‖ ^ 2 ≠ 0) :
    ‖finiteHead H qOne‖ ^ 2 +
      (inner ℝ limitingResidual (finiteHead H qOne)) ^ 2 / ‖tail H limitingResidual‖ ^ 2 ≤
      ‖F‖ ^ 2 := by
  have h := exact_head_residual_completion H F hF hh ht
  dsimp only at h
  nlinarith [sq_nonneg ‖F - finiteHead H qOne +
    (inner ℝ limitingResidual (finiteHead H qOne) / ‖tail H limitingResidual‖ ^ 2) •
      tail H limitingResidual‖]

/-- No choice of periods or legal coefficients avoids this obstruction when
the actual squarefree residual is nonzero and the exact heads are cofinal. -/
theorem error_norm_tendsto_atTop_of_residual_ne_zero
    (hr : limitingResidual ≠ 0) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (F : ℕ → QHilbert) (hF : ∀ n, F n ∈ qSquarefreeCRTSpan)
    (hh : ∀ n k, 0 < k → k ≤ H n → qSequence (F n) k = 1) :
    Tendsto (fun n => ‖qOne - F n‖) atTop atTop := by
  have ht : Tendsto (fun n => ‖tail (H n) limitingResidual‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, norm_zero] using
      ((tail_tendsto_zero limitingResidual).comp hH).norm
  have hc : 0 < ‖limitingResidual‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hr)
  apply tendsto_atTop.2
  intro B
  let b : ℝ := max B 0 + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hBb : B < b := by dsimp [b]; linarith [le_max_left B 0]
  have hsmall := (tendsto_order.mp ht).2 (‖limitingResidual‖ ^ 2 / b) (div_pos hc hb)
  filter_upwards [hsmall] with n hn
  have hprod : ‖tail (H n) limitingResidual‖ * b < ‖limitingResidual‖ ^ 2 :=
    (lt_div_iff₀ hb).mp hn
  have hpair := residual_sq_le_tail_mul_error (H n) (F n) (hF n) (hh n)
  by_contra hbad
  have hE : ‖qOne - F n‖ ≤ b := (le_of_not_ge hbad).trans hBb.le
  have hm := mul_le_mul_of_nonneg_left hE (norm_nonneg (tail (H n) limitingResidual))
  linarith

/-- The complete energies themselves diverge under the same nonzero-residual
hypothesis; this applies to constrained minima as well as other witnesses. -/
theorem energy_tendsto_atTop_of_residual_ne_zero
    (hr : limitingResidual ≠ 0) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (F : ℕ → QHilbert) (hF : ∀ n, F n ∈ qSquarefreeCRTSpan)
    (hh : ∀ n k, 0 < k → k ≤ H n → qSequence (F n) k = 1) :
    Tendsto (fun n => ‖F n‖ ^ 2) atTop atTop := by
  have he := error_norm_tendsto_atTop_of_residual_ne_zero hr H hH F hF hh
  have hn : Tendsto (fun n => ‖F n‖) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    have hg := he.eventually (eventually_ge_atTop (B + 1))
    filter_upwards [hg] with n hgn
    have htri := norm_sub_le qOne (F n)
    rw [qOne_norm] at htri
    linarith
  apply tendsto_atTop.2
  intro B
  have hg := hn.eventually (eventually_ge_atTop (max B 1))
  filter_upwards [hg] with n hgn
  have hB : B ≤ ‖F n‖ := (le_max_left B 1).trans hgn
  have h1 : 1 ≤ ‖F n‖ := (le_max_right B 1).trans hgn
  have hp := mul_nonneg (norm_nonneg (F n)) (sub_nonneg.mpr h1)
  nlinarith

/-- Even a bound on infinitely many selected exact-head errors forces zero
residual. A bound for the whole canonical schedule is unnecessary. -/
theorem residual_eq_zero_of_frequently_bounded_exact_heads
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (F : ℕ → QHilbert) (hF : ∀ n, F n ∈ qSquarefreeCRTSpan)
    (hh : ∀ n k, 0 < k → k ≤ H n → qSequence (F n) k = 1)
    (C : ℝ) (hC : ∃ᶠ n in atTop, ‖qOne - F n‖ ≤ C) :
    limitingResidual = 0 := by
  by_contra hr
  have ht := error_norm_tendsto_atTop_of_residual_ne_zero hr H hH F hF hh
  have hg := ht.eventually (eventually_gt_atTop C)
  obtain ⟨n, hn, hgt⟩ := (hC.and_eventually hg).exists
  exact (not_lt_of_ge hn) hgt

theorem residual_eq_zero_of_frequently_bounded_exact_head_energies
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (F : ℕ → QHilbert) (hF : ∀ n, F n ∈ qSquarefreeCRTSpan)
    (hh : ∀ n k, 0 < k → k ≤ H n → qSequence (F n) k = 1)
    (C : ℝ) (hC : ∃ᶠ n in atTop, ‖F n‖ ^ 2 ≤ C) :
    limitingResidual = 0 := by
  by_contra hr
  have ht := energy_tendsto_atTop_of_residual_ne_zero hr H hH F hF hh
  have hg := ht.eventually (eventually_gt_atTop C)
  obtain ⟨n, hn, hgt⟩ := (hC.and_eventually hg).exists
  exact (not_lt_of_ge hn) hgt


/-- In particular, the actual constrained primorial minima have the same
conditional divergence, for every schedule with cofinal feasible heads. -/
theorem minimumAt_energy_tendsto_atTop_of_residual_ne_zero
    (hr : limitingResidual ≠ 0) (σ H : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (hhead : ∀ n, H n ≤ σ n + 1) :
    Tendsto (fun n => ‖QCRTPeriodHeadBalance.minimumAt (σ n) (H n)‖ ^ 2)
      atTop atTop := by
  apply energy_tendsto_atTop_of_residual_ne_zero hr H hH
  · intro n
    exact QCRTPeriodHeadBalance.minimumAt_legal (σ n) (H n)
  · intro n
    exact QCRTPeriodHeadBalance.minimumAt_head (σ n) (H n) (hhead n)

/-- The missing weak test is the actual residual itself. Convergence of this
single moment for legal vectors is already equivalent to residual vanishing. -/
theorem residual_moment_tendsto_iff (F : ℕ → QHilbert)
    (hF : ∀ n, F n ∈ qSquarefreeCRTSpan) :
    Tendsto (fun n => inner ℝ limitingResidual (F n)) atTop
      (𝓝 (inner ℝ limitingResidual qOne)) ↔ limitingResidual = 0 := by
  have hz (n : ℕ) : inner ℝ limitingResidual (F n) = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal
      (legal_mem_optimizer_closure (F n) (hF n)) limitingResidual_mem_squarefree_orthogonal
  constructor
  · intro ht
    have ht0 : Tendsto (fun n => inner ℝ limitingResidual (F n)) atTop (𝓝 0) := by
      simpa only [hz] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have hm := tendsto_nhds_unique ht ht0
    have hmean : inner ℝ limitingResidual qOne = ‖limitingResidual‖ ^ 2 :=
      qResidual_inner_qOne ZetaTwoOptimizerStage.closure
    rw [hmean] at hm
    have hn : ‖limitingResidual‖ = 0 := by nlinarith [norm_nonneg limitingResidual]
    exact norm_eq_zero.mp hn
  · intro hr
    simp only [hr, inner_zero_left]
    exact tendsto_const_nhds

end RiemannResearch.RH.QSquarefreeExactHeadResidualBarrier
