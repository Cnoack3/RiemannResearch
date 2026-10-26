/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.StretchedTailWeights
import RiemannResearch.RH.QStretchedTailEnergy
import RiemannResearch.RH.QSquarefreeLogResidualTail
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QScaledTailPerturbation
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QProjectionMoments
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Critical stretched-tail criteria for the actual squarefree residual

The unconditional complete exact-head estimate already transferred in
`QSquarefreeLogResidualTail` supplies one positive arithmetic exponent.
At its exact stretched tail weight, vanishing along any one cofinal sequence
forces a squarefree annihilator to have zero mean. Applied to the actual
residual or its projected reciprocal correction, this supplies conditional
RH criteria. The requisite tail upper bound remains an arithmetic hypothesis.

The proof keeps the complete tails. The ordinary unweighted tail limit
absorbs the constant term of the exact-head energy provider; the bounded
physical reciprocal source is negligible at the stretched scale.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeStretchedTailCriterion
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QAnnihilatorTailEscape QSquarefreeResidualTail QSquarefreeSmoothedProjection
open QShiftedReciprocal QSquarefreeLogResidualTail QStretchedTailEnergy
open RiemannResearch.Analysis.StretchedTailWeights

/-- A generic squarefree annihilator consumer for the exact critical
arithmetic tail scale. The complete ordinary tail tends to zero and absorbs
the constant term in the existing stretched provider. -/
theorem annihilator_mean_zero_of_critical_tail
    (a C : ℝ)
    (hprovider : ∀ᶠ N : ℕ in atTop, ∀ u : QHilbert,
      u ∈ ZetaTwoOptimizerStage.closureᗮ →
        (inner ℝ qOne u) ^ 2 ≤
          (16 / zetaTwo + C * arithmeticWeight a N) * ‖tail N u‖ ^ 2)
    (u : QHilbert) (hu : u ∈ ZetaTwoOptimizerStage.closureᗮ)
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop)
    (hsmall : Tendsto (fun j => arithmeticWeight a (q j) * ‖tail (q j) u‖ ^ 2)
      atTop (𝓝 0)) : inner ℝ qOne u = 0 := by
  have ht : Tendsto (fun j => ‖tail (q j) u‖ ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      ((tail_tendsto_zero u).comp hq).norm.pow 2
  have hlim := (ht.const_mul (16 / zetaTwo)).add (hsmall.const_mul C)
  simp only [Function.comp_def, mul_zero, zero_add] at hlim
  have hle : ∀ᶠ j in atTop, (inner ℝ qOne u) ^ 2 ≤
      (16 / zetaTwo) * ‖tail (q j) u‖ ^ 2 +
        C * (arithmeticWeight a (q j) * ‖tail (q j) u‖ ^ 2) := by
    filter_upwards [hq.eventually hprovider] with j hj
    have h := hj u hu
    nlinarith
  have hz : (inner ℝ qOne u) ^ 2 ≤ 0 := ge_of_tendsto hlim hle
  nlinarith [sq_nonneg (inner ℝ qOne u)]

/-- One positive arithmetic exponent, supplied unconditionally by the
existing exact-head estimate, works for all squarefree annihilators. -/
theorem exists_critical_stretched_annihilator_criterion :
    ∃ a : ℝ, 0 < a ∧ ∀ u : QHilbert,
      u ∈ ZetaTwoOptimizerStage.closureᗮ → ∀ q : ℕ → ℕ,
        Tendsto q atTop atTop →
        Tendsto (fun j => arithmeticWeight a (q j) * ‖tail (q j) u‖ ^ 2)
          atTop (𝓝 0) → inner ℝ qOne u = 0 := by
  obtain ⟨a, ha, C, hC, hp⟩ := squarefree_annihilator_eventual_stretched_tail_bound
  refine ⟨a, ha, ?_⟩
  intro u hu q hq hsmall
  apply annihilator_mean_zero_of_critical_tail a C _ u hu q hq hsmall
  filter_upwards [hp] with N hN
  intro v hv
  simpa only [arithmeticWeight, arithmeticDecay, mul_assoc] using hN v hv

/-- The actual squarefree residual has the same critical-tail sufficient
criterion; no converse implication from RH is used. -/
theorem exists_critical_stretched_residual_tail_criterion :
    ∃ a : ℝ, 0 < a ∧ ∀ q : ℕ → ℕ, Tendsto q atTop atTop →
      Tendsto (fun j => arithmeticWeight a (q j) * residualTailEnergy (q j))
        atTop (𝓝 0) → RiemannHypothesis := by
  obtain ⟨a, ha, hcriterion⟩ := exists_critical_stretched_annihilator_criterion
  refine ⟨a, ha, ?_⟩
  intro q hq hsmall
  have hmean := hcriterion limitingResidual
    limitingResidual_mem_squarefree_orthogonal q hq hsmall
  have hm : inner ℝ qOne limitingResidual = ‖limitingResidual‖ ^ 2 := by
    rw [real_inner_comm]
    exact qResidual_inner_qOne ZetaTwoOptimizerStage.closure
  rw [hm] at hmean
  have hn : ‖limitingResidual‖ = 0 := by
    nlinarith [norm_nonneg limitingResidual]
  have hr : limitingResidual = 0 := norm_eq_zero.mp hn
  have hmem : qOne ∈ ZetaTwoOptimizerStage.closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hmem)

/-- New weaker sufficient RH criterion: the actual correction need only
have vanishing critical stretched-weight tail along one cofinal sequence.
The positive exponent is fixed by the unconditional arithmetic provider. -/
theorem exists_critical_stretched_correction_tail_criterion :
    ∃ a : ℝ, 0 < a ∧ ∀ q : ℕ → ℕ, Tendsto q atTop atTop →
      Tendsto (fun j => arithmeticWeight a (q j) * ‖tail (q j) correction‖ ^ 2)
        atTop (𝓝 0) → RiemannHypothesis := by
  obtain ⟨a, ha, hcriterion⟩ := exists_critical_stretched_annihilator_criterion
  refine ⟨a, ha, ?_⟩
  intro q hq hsmall
  have hBr := (arithmeticWeight_B_tail_tendsto_zero a ha limitingResidual).comp hq
  have hscreen : Tendsto
      (fun j => arithmeticWeight a (q j) * ‖tail (q j) screened‖ ^ 2)
        atTop (𝓝 0) := by
    have hlim := (hBr.const_mul 2).add (hsmall.const_mul 2)
    simp only [Function.comp_def, mul_zero, zero_add] at hlim
    apply squeeze_zero
      (fun j => mul_nonneg (arithmeticWeight_nonneg a (q j)) (sq_nonneg _)) _ hlim
    intro j
    have hn : ‖tail (q j) screened‖ ≤
        ‖tail (q j) (B limitingResidual)‖ + ‖tail (q j) correction‖ := by
      rw [screened, tail_sub]
      exact norm_sub_le _ _
    have hs : ‖tail (q j) screened‖ ^ 2 ≤
        2 * ‖tail (q j) (B limitingResidual)‖ ^ 2 +
          2 * ‖tail (q j) correction‖ ^ 2 := by
      nlinarith [norm_nonneg (tail (q j) screened),
        norm_nonneg (tail (q j) (B limitingResidual)),
        norm_nonneg (tail (q j) correction),
        sq_nonneg (‖tail (q j) (B limitingResidual)‖ - ‖tail (q j) correction‖)]
    have hm := mul_le_mul_of_nonneg_left hs (arithmeticWeight_nonneg a (q j))
    nlinarith
  have hmean := hcriterion screened screened_mem_orthogonal q hq hscreen
  rw [screened_mean_eq_energy] at hmean
  have hr : limitingResidual = 0 := B_faithful limitingResidual hmean
  have hm : qOne ∈ ZetaTwoOptimizerStage.closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

/-- An unconditional positive stretched exponent works simultaneously for
all nonzero-mean annihilators of the actual squarefree closure. -/
theorem exists_stretched_annihilator_tail_escape :
    ∃ a : ℝ, 0 < a ∧ ∀ u : QHilbert,
      u ∈ ZetaTwoOptimizerStage.closureᗮ → inner ℝ qOne u ≠ 0 →
        Tendsto (fun N => arithmeticWeight a N * ‖tail N u‖ ^ 2) atTop atTop := by
  obtain ⟨a, ha, C, hC, hp⟩ := squarefree_annihilator_eventual_stretched_tail_bound
  refine ⟨a / 2, by positivity, ?_⟩
  intro u hu hm
  have hc : 0 < (inner ℝ qOne u) ^ 2 := sq_pos_of_ne_zero hm
  have ht : Tendsto (fun N => ‖tail N u‖ ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      (tail_tendsto_zero u).norm.pow 2
  apply tendsto_atTop.2
  intro B
  let b : ℝ := max B 0 + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hBb : B < b := by dsimp [b]; linarith [le_max_left B 0]
  have hlim := (ht.const_mul (16 / zetaTwo)).add
    ((arithmeticDecay_tendsto_zero (a / 2) (by positivity)).const_mul (C * b))
  simp only [Function.comp_def, mul_zero, zero_add] at hlim
  have hupper := (tendsto_order.1 hlim).2 _ hc
  filter_upwards [hp, hupper] with N hN hsmall
  by_contra hbad
  have hbounded : arithmeticWeight (a / 2) N * ‖tail N u‖ ^ 2 ≤ b :=
    (le_of_not_ge hbad).trans hBb.le
  have hprod := mul_le_mul_of_nonneg_left hbounded
    (mul_nonneg hC (arithmeticDecay_pos (a / 2) N).le)
  have hpair : (inner ℝ qOne u) ^ 2 ≤
      (16 / zetaTwo + C * arithmeticWeight a N) * ‖tail N u‖ ^ 2 := by
    simpa only [arithmeticWeight, arithmeticDecay, mul_assoc] using hN u hu
  have hcontr : (inner ℝ qOne u) ^ 2 < (inner ℝ qOne u) ^ 2 := by
    calc
      (inner ℝ qOne u) ^ 2
          ≤ (16 / zetaTwo + C * arithmeticWeight a N) * ‖tail N u‖ ^ 2 := hpair
      _ = (16 / zetaTwo) * ‖tail N u‖ ^ 2 +
          (C * arithmeticDecay (a / 2) N) *
            (arithmeticWeight (a / 2) N * ‖tail N u‖ ^ 2) := by
        rw [arithmeticWeight_eq_half]
        ring
      _ ≤ (16 / zetaTwo) * ‖tail N u‖ ^ 2 +
          (C * arithmeticDecay (a / 2) N) * b := add_le_add le_rfl hprod
      _ = (16 / zetaTwo) * ‖tail N u‖ ^ 2 +
          (C * b) * arithmeticDecay (a / 2) N := by ring
      _ < (inner ℝ qOne u) ^ 2 := hsmall
  exact (lt_irrefl _ hcontr)

/-- The actual correction has the same unconditional stretched escape on
the nonzero-residual branch. -/
theorem exists_stretched_correction_tail_escape :
    ∃ a : ℝ, 0 < a ∧ (limitingResidual ≠ 0 →
      Tendsto (fun N => arithmeticWeight a N * ‖tail N correction‖ ^ 2)
        atTop atTop) := by
  obtain ⟨a, ha, hescape⟩ := exists_stretched_annihilator_tail_escape
  refine ⟨a, ha, ?_⟩
  intro hr
  have hs := hescape screened screened_mem_orthogonal (by
    rw [screened_mean_eq_energy]
    exact fun h => hr (B_faithful limitingResidual h))
  have hBr := arithmeticWeight_B_tail_tendsto_zero a ha limitingResidual
  apply tendsto_atTop.2
  intro C
  have hBrSmall := (tendsto_order.1 hBr).2 _ (zero_lt_one : (0 : ℝ) < 1)
  have hsLarge := hs.eventually (eventually_ge_atTop (2 + 2 * C))
  filter_upwards [hBrSmall, hsLarge] with N hf hg
  have hn : ‖tail N screened‖ ≤
      ‖tail N (B limitingResidual)‖ + ‖tail N correction‖ := by
    rw [screened, tail_sub]
    exact norm_sub_le _ _
  have hn2 : ‖tail N screened‖ ^ 2 ≤
      2 * ‖tail N (B limitingResidual)‖ ^ 2 + 2 * ‖tail N correction‖ ^ 2 := by
    nlinarith [norm_nonneg (tail N screened),
      norm_nonneg (tail N (B limitingResidual)), norm_nonneg (tail N correction),
      sq_nonneg (‖tail N (B limitingResidual)‖ - ‖tail N correction‖)]
  have hmul := mul_le_mul_of_nonneg_left hn2 (arithmeticWeight_nonneg a N)
  nlinarith

end RiemannResearch.RH.QSquarefreeStretchedTailCriterion
