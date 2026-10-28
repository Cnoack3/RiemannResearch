/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.StretchedTailWeights
import RiemannResearch.RH.QSquarefreeStretchedTailCriterion
import RiemannResearch.RH.QSquarefreeInterpolationRigidity
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QStretchedTailEnergy
import RiemannResearch.RH.QScaledTailPerturbation
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.Linarith

/-!
# Stretched-tail criteria for the actual squarefree projection displacement

Source: the user's change-of-measure and full-to-squarefree tail agenda,
28 October 2026. The unconditional exact-head bound has already been
transferred to squarefree annihilators using legal prime anchors. This module
applies that bound to the actual witness `B pResidual - displacement`, keeping
its complete signed tail identity. The reciprocal source has vanishing
stretched-weight tails, so the displacement inherits the annihilator's escape.

The bounded-tail and vanishing-tail conditions remain OPEN arithmetic
obligations. They are not consequences of Hilbert norm boundedness.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeStretchedDisplacement
open ZetaTwoHilbert ZetaTwoOptimizerStage QFiniteSupportDualCriterion
open QAnnihilatorTailEscape QShiftedReciprocal QSquarefreeDisplacementRigidity
open QSquarefreeStretchedTailCriterion QStretchedTailEnergy
open RiemannResearch.Analysis.StretchedTailWeights

/-- Complete signed tail identity for the actual measure-change witness. -/
theorem witness_tail_energy_exact (N : ℕ) :
    ‖tail N witness‖ ^ 2 = ‖tail N (B pResidual)‖ ^ 2 +
      ‖tail N displacement‖ ^ 2 -
        2 * inner ℝ (tail N (B pResidual)) (tail N displacement) := by
  exact tail_sub_energy_exact N (B pResidual) displacement

/-- A single unconditional positive arithmetic exponent works for the actual
displacement whenever the actual squarefree residual is nonzero. -/
theorem exists_stretched_displacement_tail_escape :
    ∃ a : ℝ, 0 < a ∧ (limitingResidual ≠ 0 →
      Tendsto (fun N => arithmeticWeight a N * ‖tail N displacement‖ ^ 2)
        atTop atTop) := by
  obtain ⟨a, ha, hescape⟩ := exists_stretched_annihilator_tail_escape
  refine ⟨a, ha, ?_⟩
  intro hr
  apply weighted_tail_transfer_sub (B pResidual) displacement (arithmeticWeight a)
    (Eventually.of_forall (arithmeticWeight_nonneg a)) 1
  · filter_upwards [((tendsto_order.1
      (arithmeticWeight_B_tail_tendsto_zero a ha pResidual)).2 _
        (zero_lt_one : (0 : ℝ) < 1))] with N hN
    exact hN.le
  · exact hescape witness witness_mem_orthogonal
      (fun hm => hr (residual_eq_zero_of_witness_mean_zero hm))

/-- Conditional research reduction. Frequent boundedness at this stretched
scale is exactly equivalent to residual vanishing; no bound is supplied. -/
theorem exists_residual_zero_iff_frequently_bounded_stretched_displacement_tail :
    ∃ a : ℝ, 0 < a ∧ (limitingResidual = 0 ↔
      ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
        arithmeticWeight a N * ‖tail N displacement‖ ^ 2 ≤ C) := by
  obtain ⟨a, ha, hescape⟩ := exists_stretched_displacement_tail_escape
  refine ⟨a, ha, ?_⟩
  constructor
  · intro hr
    refine ⟨0, (Eventually.of_forall ?_).frequently⟩
    intro N
    rw [displacement_eq_zero_of_residual_eq_zero hr]
    simp [tail, finiteHead]
  · rintro ⟨C, hC⟩
    by_contra hr
    have hg := (hescape hr).eventually (eventually_gt_atTop C)
    obtain ⟨N, hN, hgt⟩ := (hC.and_eventually hg).exists
    exact (not_lt_of_ge hN) hgt

/-- At the critical arithmetic exponent, vanishing of the weighted complete
displacement tail along one cofinal sequence forces the residual to vanish. -/
theorem exists_critical_stretched_displacement_tail_criterion :
    ∃ a : ℝ, 0 < a ∧ ∀ q : ℕ → ℕ, Tendsto q atTop atTop →
      Tendsto (fun j => arithmeticWeight a (q j) * ‖tail (q j) displacement‖ ^ 2)
        atTop (𝓝 0) → limitingResidual = 0 := by
  obtain ⟨a, ha, hcriterion⟩ := exists_critical_stretched_annihilator_criterion
  refine ⟨a, ha, ?_⟩
  intro q hq hsmall
  have hBr := (arithmeticWeight_B_tail_tendsto_zero a ha pResidual).comp hq
  have hwitness : Tendsto
      (fun j => arithmeticWeight a (q j) * ‖tail (q j) witness‖ ^ 2)
        atTop (𝓝 0) := by
    have hlim := (hBr.const_mul 2).add (hsmall.const_mul 2)
    simp only [Function.comp_def, mul_zero, zero_add] at hlim
    apply squeeze_zero
      (fun j => mul_nonneg (arithmeticWeight_nonneg a (q j)) (sq_nonneg _)) _ hlim
    intro j
    have hn : ‖tail (q j) witness‖ ≤
        ‖tail (q j) (B pResidual)‖ + ‖tail (q j) displacement‖ := by
      rw [witness, tail_sub]
      exact norm_sub_le _ _
    have hs : ‖tail (q j) witness‖ ^ 2 ≤
        2 * ‖tail (q j) (B pResidual)‖ ^ 2 +
          2 * ‖tail (q j) displacement‖ ^ 2 := by
      nlinarith [norm_nonneg (tail (q j) witness),
        norm_nonneg (tail (q j) (B pResidual)),
        norm_nonneg (tail (q j) displacement),
        sq_nonneg
          (‖tail (q j) (B pResidual)‖ - ‖tail (q j) displacement‖)]
    have hm := mul_le_mul_of_nonneg_left hs (arithmeticWeight_nonneg a (q j))
    nlinarith
  exact residual_eq_zero_of_witness_mean_zero
    (hcriterion witness witness_mem_orthogonal q hq hwitness)

open QSquarefreeInterpolationRigidity

/-- One arithmetic exponent works for every fixed positive interpolation
parameter at most one. Convergence is not asserted uniformly in the parameter. -/
theorem exists_stretched_interpolation_tail_escape :
    ∃ a : ℝ, 0 < a ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ d : QHilbert,
      closure.starProjection (t • B (limitingResidual + d)) = d →
      limitingResidual ≠ 0 →
        Tendsto (fun N => arithmeticWeight a N * ‖tail N d‖ ^ 2)
          atTop atTop := by
  obtain ⟨a, ha, hescape⟩ := exists_stretched_annihilator_tail_escape
  refine ⟨a, ha, ?_⟩
  intro t ht ht1 d hnormal hr
  have hsource := arithmeticWeight_B_tail_tendsto_zero a ha
    (t • (limitingResidual + d))
  simp only [map_smul] at hsource
  apply weighted_tail_transfer_sub (t • B (limitingResidual + d)) d
    (arithmeticWeight a) (Eventually.of_forall (arithmeticWeight_nonneg a)) 1
  · filter_upwards [((tendsto_order.1 hsource).2 _
      (zero_lt_one : (0 : ℝ) < 1))] with N hN
    exact hN.le
  · exact hescape (interpolationWitness t d)
      (interpolationWitness_mem_orthogonal t d hnormal)
      (fun hm => hr
        (residual_zero_of_interpolationWitness_mean_zero t ht ht1 d hnormal hm))


/-- At every positive point of the constructed path, the same stretched tail
bound is equivalent to residual vanishing. The upper bound remains Open. -/
theorem exists_path_residual_zero_iff_frequent_stretched_tail :
    ∃ a : ℝ, 0 < a ∧ ∀ (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1),
      (limitingResidual = 0 ↔ ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
        arithmeticWeight a N * ‖tail N (pathDisplacement t ht.le ht1)‖ ^ 2 ≤ C) := by
  obtain ⟨a, ha, hescape⟩ := exists_stretched_interpolation_tail_escape
  refine ⟨a, ha, ?_⟩
  intro t ht ht1
  constructor
  · intro hr
    refine ⟨0, (Eventually.of_forall ?_).frequently⟩
    intro N
    rw [pathDisplacement_eq_zero_of_residual_eq_zero t ht.le ht1 hr]
    simp [tail, finiteHead]
  · rintro ⟨C, hC⟩
    by_contra hr
    have he := hescape t ht ht1 (pathDisplacement t ht.le ht1)
      (pathDisplacement_normal t ht.le ht1) hr
    obtain ⟨N, hN, hgt⟩ :=
      (hC.and_eventually (he.eventually (eventually_gt_atTop C))).exists
    exact (not_lt_of_ge hN) hgt

end RiemannResearch.RH.QSquarefreeStretchedDisplacement
