/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QMobiusStretchedEnergy
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.RH.QScaledTailPerturbation
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QProjectionMoments
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.Analysis.LogTailWeights
import RiemannResearch.Analysis.StretchedExponentialBounds
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Logarithmic and stretched tail escape in the actual squarefree Q space

Source: the user-provided moving-head research handoff, 26 October 2026.
The arithmetic inputs are the existing unconditional exact-head energy
bounds. A Bertrand-prime anchor supplies legal squarefree heads at comparable
cutoffs, without equating squarefree and all-conductor annihilator spaces.

The complete signed tail identities precede the perturbation estimates in
QScaledTailPerturbation. The final RH theorem permits a fixed polylogarithmic
moving-head envelope. That actual envelope remains an Open arithmetic
obligation; the theorem is a conditional research reduction.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeLogResidualTail
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QAnnihilatorTailEscape QSquarefreeResidualTail QFiniteSupportDualCriterion
open RiemannResearch.Analysis.LogTailWeights QPolylogTailEnergy

/-- Every squarefree annihilator with nonzero mean escapes every fixed
logarithmic tail scale. This is an unconditional squarefree transfer. -/
theorem squarefree_annihilator_log_scaled_tail_tendsto
    (u : QHilbert) (hu : u ∈ ZetaTwoOptimizerStage.closureᗮ)
    (hm : inner ℝ qOne u ≠ 0) (k : ℕ) :
    Tendsto (fun N : ℕ => logWeight k N * ‖tail N u‖ ^ 2) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  let b : ℝ := max B 0 + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hBb : B < b := by dsimp [b]; linarith [le_max_left B 0]
  have hc : 0 < (inner ℝ qOne u) ^ 2 := sq_pos_of_ne_zero hm
  have heps : 0 < (inner ℝ qOne u) ^ 2 / (2 * b) :=
    div_pos hc (by positivity)
  have ht := (tendsto_order.1 (defect_sq_log_weight_tendsto_zero k)).2 _ heps
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 ht
  filter_upwards [eventually_ge_atTop (max N0 1)] with N hN
  have hNpos : 0 < N := by omega
  obtain ⟨p, hp, hNp, hp2⟩ :=
    Nat.exists_prime_lt_and_le_two_mul N (Nat.ne_of_gt hNpos)
  let M : ℕ := p - 1
  have hNM : N ≤ M := by dsimp [M]; omega
  have hMp : M + 1 = p := by dsimp [M]; omega
  have hsf : Squarefree (M + 1) := by rw [hMp]; exact hp.squarefree
  have hMpos : 0 < M := by omega
  have hM2N : M ≤ 2 * N := by dsimp [M]; omega
  have hs : ‖defect M‖ ^ 2 / logWeight k M <
      (inner ℝ qOne u) ^ 2 / (2 * b) := hN0 M (by omega)
  have hcross : ‖defect M‖ ^ 2 * (2 * b) <
      (inner ℝ qOne u) ^ 2 * logWeight k M :=
    (div_lt_div_iff₀ (logWeight_pos k M hMpos)
      (by positivity : 0 < 2 * b)).mp hs
  have hscale := mul_le_mul_of_nonneg_left
    (logWeight_le_two_of_comparable k N M hNpos hNM hM2N) hc.le
  have hsmall : ‖defect M‖ ^ 2 * b <
      (inner ℝ qOne u) ^ 2 * logWeight k N := by nlinarith
  have hpair := squarefree_defect_tail_sq_bound N M hNM hsf u hu
  have hpairN := mul_le_mul_of_nonneg_right hpair (logWeight_nonneg k N)
  by_contra hbad
  have htail : logWeight k N * ‖tail N u‖ ^ 2 ≤ b :=
    (le_of_not_ge hbad).trans hBb.le
  have hprod := mul_le_mul_of_nonneg_left htail (sq_nonneg ‖defect M‖)
  nlinarith

theorem log_scaled_residual_tail_tendsto_of_ne_zero
    (hr : limitingResidual ≠ 0) (k : ℕ) :
    Tendsto (fun N : ℕ => logWeight k N * residualTailEnergy N) atTop atTop := by
  apply squarefree_annihilator_log_scaled_tail_tendsto limitingResidual
    limitingResidual_mem_squarefree_orthogonal
  have hm : inner ℝ qOne limitingResidual = ‖limitingResidual‖ ^ 2 := by
    rw [real_inner_comm]
    exact qResidual_inner_qOne ZetaTwoOptimizerStage.closure
  rw [hm]
  exact ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hr))

/-- Exact actual-residual criterion, now allowing any fixed logarithmic
loss. The upper-bound side is not asserted unconditionally. -/
theorem residual_zero_iff_frequently_bounded_log_scaled_tail (k : ℕ) :
    limitingResidual = 0 ↔ ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      logWeight k N * residualTailEnergy N ≤ C := by
  constructor
  · intro hr
    refine ⟨0, (Eventually.of_forall ?_).frequently⟩
    intro N
    simp [residualTailEnergy, tail, finiteHead, hr]
  · rintro ⟨C, hC⟩
    by_contra hr
    have hg := (log_scaled_residual_tail_tendsto_of_ne_zero hr k).eventually
      (eventually_gt_atTop C)
    obtain ⟨N, hN, hgt⟩ := (hC.and_eventually hg).exists
    exact (not_lt_of_ge hN) hgt

theorem riemannHypothesis_of_cofinal_squarefree_log_tail_bound
    (k : ℕ) (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (C : ℝ)
    (hbound : ∀ j, logWeight k (q j) * residualTailEnergy (q j) ≤ C) :
    RiemannHypothesis := by
  have hr : limitingResidual = 0 := by
    by_contra hr
    have ht := (log_scaled_residual_tail_tendsto_of_ne_zero hr k).comp hq
    obtain ⟨j, hj⟩ := (ht.eventually (eventually_gt_atTop C)).exists
    exact (not_lt_of_ge (hbound j)) hj
  have hm : qOne ∈ ZetaTwoOptimizerStage.closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

open QShiftedReciprocal QSquarefreeSmoothedProjection

/-- The actual projected smoothed correction also escapes every fixed
logarithmic tail scale if the actual squarefree residual is nonzero. -/
theorem correction_log_scaled_tail_tendsto
    (hr : limitingResidual ≠ 0) (k : ℕ) :
    Tendsto (fun N : ℕ => logWeight k N * ‖tail N correction‖ ^ 2)
      atTop atTop := by
  apply weighted_tail_transfer_sub (B limitingResidual) correction (logWeight k)
    (Eventually.of_forall (logWeight_nonneg k))
    (2 * (Real.sqrt zetaTwo * ‖limitingResidual‖) ^ 2 / zetaTwo)
  · apply Eventually.of_forall
    intro N
    calc
      logWeight k N * ‖tail N (B limitingResidual)‖ ^ 2
          ≤ (N : ℝ) * ‖tail N (B limitingResidual)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (logWeight_le_nat k N) (sq_nonneg _)
      _ ≤ _ := scaled_tail_energy_le_of_bounded (B limitingResidual) N
        (Real.sqrt zetaTwo * ‖limitingResidual‖) (by positivity)
        (B_physical_bound limitingResidual)
  · exact squarefree_annihilator_log_scaled_tail_tendsto screened
      screened_mem_orthogonal (by
        rw [screened_mean_eq_energy]
        exact fun h => hr (B_faithful limitingResidual h)) k

/-- The finite logarithmic exponent may be chosen arbitrarily. -/
theorem residual_zero_iff_correction_frequently_bounded_log_scaled_tail (k : ℕ) :
    limitingResidual = 0 ↔ ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      logWeight k N * ‖tail N correction‖ ^ 2 ≤ C := by
  constructor
  · intro hr
    refine ⟨0, (Eventually.of_forall ?_).frequently⟩
    intro N
    simp [correction, hr, tail, finiteHead]
  · rintro ⟨C, hC⟩
    by_contra hr
    have hg := (correction_log_scaled_tail_tendsto hr k).eventually
      (eventually_gt_atTop C)
    obtain ⟨N, hN, hgt⟩ := (hC.and_eventually hg).exists
    exact (not_lt_of_ge hN) hgt

theorem riemannHypothesis_of_cofinal_correction_log_tail_bound
    (k : ℕ) (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (C : ℝ)
    (hbound : ∀ j, logWeight k (q j) * ‖tail (q j) correction‖ ^ 2 ≤ C) :
    RiemannHypothesis := by
  have hr : limitingResidual = 0 := by
    by_contra hr
    have ht := (correction_log_scaled_tail_tendsto hr k).comp hq
    obtain ⟨j, hj⟩ := (ht.eventually (eventually_gt_atTop C)).exists
    exact (not_lt_of_ge (hbound j)) hj
  have hm : qOne ∈ ZetaTwoOptimizerStage.closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

open RiemannResearch.Analysis QMobiusStretchedEnergy

/-- A quantitative complete-tail lower inequality, uniform over all squarefree
annihilators. The stretched-exponential arithmetic constants are unconditional. -/
theorem squarefree_annihilator_eventual_stretched_tail_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ u : QHilbert, u ∈ ZetaTwoOptimizerStage.closureᗮ →
        (inner ℝ qOne u) ^ 2 ≤
          (16 / zetaTwo + C * (N : ℝ) *
            Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ)))) *
              ‖tail N u‖ ^ 2 := by
  obtain ⟨a, ha, C, hC, hbound⟩ := exactHead_error_eventual_stretched_energy
  refine ⟨a, ha, 2 * C, by positivity, ?_⟩
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hbound
  filter_upwards [eventually_ge_atTop (max N0 1)] with N hN
  intro u hu
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  obtain ⟨p, hp, hNp, hp2⟩ :=
    Nat.exists_prime_lt_and_le_two_mul N (Nat.ne_of_gt hNpos)
  let M : ℕ := p - 1
  have hNM : N ≤ M := by dsimp [M]; omega
  have hMp : M + 1 = p := by dsimp [M]; omega
  have hsf : Squarefree (M + 1) := by rw [hMp]; exact hp.squarefree
  have hNMR : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hM2NR : (M : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show M ≤ 2 * N by dsimp [M]; omega)
  have hlog : Real.log (N : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log hNR hNMR
  have hphi : logProductPower (1 / 11) (6 + Real.log (N : ℝ)) ≤
      logProductPower (1 / 11) (6 + Real.log (M : ℝ)) :=
    logProductPower_mono (1 / 11) (by norm_num)
      (by linarith [Real.log_nonneg hN1]) (by linarith)
  have hexp :
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (M : ℝ))) ≤
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hphi (neg_nonpos.mpr ha.le))
  have hterm : C * (M : ℝ) *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (M : ℝ))) ≤
      (2 * C) * (N : ℝ) *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) := by
    calc
      _ ≤ C * (M : ℝ) *
          Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hC (Nat.cast_nonneg M))
      _ ≤ C * (2 * (N : ℝ)) *
          Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hM2NR hC) (Real.exp_pos _).le
      _ = _ := by ring
  have hdefect : ‖defect M‖ ^ 2 ≤
      16 / zetaTwo + (2 * C) * (N : ℝ) *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) := by
    have hM := hN0 M (by omega)
    change ‖defect M‖ ^ 2 ≤ _ at hM
    linarith
  exact (squarefree_defect_tail_sq_bound N M hNM hsf u hu).trans
    (mul_le_mul_of_nonneg_right hdefect (sq_nonneg ‖tail N u‖))

/-- Conditional research reduction. The common physical polylogarithmic
envelope is an open arithmetic obligation; no uniform Gram bound is used. -/
theorem riemannHypothesis_of_polylog_moving_head_bound (m : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ N n : ℕ, 0 < n → n ≤ N →
      |qSequence (movingCorrection N) n| ≤ C*(6+Real.log (n : ℝ))^m) :
    RiemannHypothesis := by
  have hlim : ∀ n : ℕ,
      |qSequence correction n| ≤ C*(6+Real.log (n : ℝ))^m := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [qSequence_zero, abs_zero, Nat.cast_zero, Real.log_zero, add_zero]
      positivity
    apply le_of_tendsto
      ((qSequence_tendsto_of_tendsto movingCorrection_tendsto n).abs)
    filter_upwards [eventually_ge_atTop n] with N hN
    exact hb N n (Nat.pos_of_ne_zero hn) hN
  obtain ⟨D, hD⟩ := exists_log_scaled_tail_bound_of_polylog correction m C hC hlim
  exact riemannHypothesis_of_cofinal_correction_log_tail_bound
    (2*m+2) id tendsto_id D hD

end RiemannResearch.RH.QSquarefreeLogResidualTail
