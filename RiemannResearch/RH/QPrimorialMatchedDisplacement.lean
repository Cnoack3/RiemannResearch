/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.QPrimeProjectionControl
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Matched Pareto and Q projections on the complete squarefree primorial tower

Source: *Squarefree projection displacement and infinite CRT carries*,
9 November 2026, Sections 6 and 12.1, 12.4. We use the existing cutoff-indexed
primorials, retaining every divisor conductor. The cofinal pairing test
requires an arithmetic upper bound on the actual normalized pairing.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QPrimorialMatchedDisplacement

open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open Pareto.SquarefreeStageExhaustion QParetoEquivalence QParetoClosedProjectionComparison
open QSquarefreePrimorialCofinality QSquarefreeMeasureRigidity QSquarefreeDisplacementRigidity
open QSquarefreeFiniteDisplacement QShiftedReciprocal QAnnihilatorTailEscape

/-- The very same complete primorial dictionary in Pareto coordinates. -/
def paretoStage (n : ℕ) : Submodule ℝ ThresholdHilbert :=
  (primorialStage n).map paretoEquiv.toLinearMap

instance (n : ℕ) : FiniteDimensional ℝ (paretoStage n) := by
  unfold paretoStage
  infer_instance

theorem toPareto_mem_stage_iff (n : ℕ) (f : QHilbert) :
    toPareto f ∈ paretoStage n ↔ f ∈ primorialStage n := by
  constructor
  · rintro ⟨g, hg, he⟩
    have h : g = f := paretoEquiv.injective he
    exact h ▸ hg
  · intro hf
    exact ⟨f, hf, rfl⟩

def pOptimizer (n : ℕ) : QHilbert := pFit (paretoStage n) qOne

def stageDisplacement (n : ℕ) : QHilbert := primorialOptimizer n - pOptimizer n

def pError (n : ℕ) : ℝ := ‖toPareto (qOne - pOptimizer n)‖ ^ 2

def normalizedPairing (n m : ℕ) : ℝ :=
  (zetaTwo * (m : ℝ)) * inner ℝ (qResidue m) (stageDisplacement n)

theorem pOptimizer_mem (n : ℕ) : pOptimizer n ∈ primorialStage n :=
  pFit_mem _ _ (toPareto_mem_stage_iff n) qOne

theorem stageDisplacement_mem (n : ℕ) : stageDisplacement n ∈ primorialStage n :=
  (primorialStage n).sub_mem ((primorialStage n).starProjection_apply_mem qOne)
    (pOptimizer_mem n)

theorem paretoStage_closure :
    (⨆ n, paretoStage n).topologicalClosure = paretoSquarefreeClosure := by
  change (⨆ n, (primorialStage n).map paretoEquiv.toLinearMap).topologicalClosure =
    (ZetaTwoOptimizerStage.closure.map paretoEquiv.toLinearMap).topologicalClosure
  rw [← Submodule.map_iSup, iSup_primorial_eq_squarefreeSpan,
    QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  ext y
  have h₁ := mem_closure_map_iff qSquarefreeCRTSpan (toQ y)
  have h₂ := mem_closure_map_iff qSquarefreeCRTSpan.topologicalClosure (toQ y)
  rw [toPareto_toQ] at h₁ h₂
  have hc : qSquarefreeCRTSpan.topologicalClosure.topologicalClosure =
      qSquarefreeCRTSpan.topologicalClosure := by
    apply SetLike.coe_injective
    exact qSquarefreeCRTSpan.isClosed_topologicalClosure.closure_eq
  rw [hc] at h₂
  exact h₁.trans h₂.symm

theorem pOptimizer_tendsto :
    Tendsto pOptimizer atTop (𝓝 (pFit paretoSquarefreeClosure qOne)) := by
  have hm : Monotone paretoStage := fun _ _ h => Submodule.map_mono (primorialStage_mono h)
  have h := Submodule.starProjection_tendsto_closure_iSup paretoStage hm (toPareto qOne)
  have h' : Tendsto (fun n => (paretoStage n).starProjection (toPareto qOne))
      atTop (𝓝 (paretoSquarefreeClosure.starProjection (toPareto qOne))) := by
    simpa only [paretoStage_closure] using h
  exact toQCLM.continuous.continuousAt.tendsto.comp h'

theorem stageDisplacement_tendsto :
    Tendsto stageDisplacement atTop (𝓝 displacement) := by
  change Tendsto (fun n => primorialOptimizer n - pOptimizer n) atTop
    (𝓝 (ZetaTwoOptimizerStage.closure.starProjection qOne - pFit paretoSquarefreeClosure qOne))
  simpa only [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure] using
    primorialOptimizer_tendsto.sub pOptimizer_tendsto

theorem pError_tendsto :
    Tendsto pError atTop (𝓝 (‖toPareto pResidual‖ ^ 2)) := by
  have h : Tendsto (fun n => qOne - pOptimizer n) atTop (𝓝 pResidual) :=
    tendsto_const_nhds.sub pOptimizer_tendsto
  exact ((toParetoCLM.continuous.tendsto _).comp h).norm.pow 2

theorem pError_le_one (n : ℕ) : pError n ≤ 1 := by
  have hunit : ‖hilbertOne‖ = 1 := by
    nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  have h := abs_real_inner_le_norm hilbertOne (toPareto (qOne - pOptimizer n))
  change |inner ℝ hilbertOne (toPareto (qOne - pFit (paretoStage n) qOne))| ≤ _
    at h
  rw [matched_pResidual_mean, abs_of_nonneg (sq_nonneg _), hunit, one_mul] at h
  change ‖toPareto (qOne - pOptimizer n)‖ ^ 2 ≤ ‖toPareto (qOne - pOptimizer n)‖ at h
  apply h.trans
  by_contra! hgt
  have hp : 0 < ‖toPareto (qOne - pOptimizer n)‖ := by linarith
  nlinarith only [h, mul_lt_mul_of_pos_left hgt hp]

theorem conductor_mem (n m : ℕ) (hm : 1 < m) (hd : m ∣ primorialPeriod n) :
    qResidue m ∈ primorialStage n :=
  Submodule.subset_span ⟨m, hm, hd, rfl⟩

theorem prime_mem (n p : ℕ) (hp : p.Prime) (hle : p ≤ n + 3) :
    qResidue p ∈ primorialStage n :=
  conductor_mem n p hp.one_lt (dvd_trans hp.squarefree.dvd_primorial (primorial_dvd_primorial hle))

/-- The error is the full signed tail of the Pareto residual, including every
physical site in each CRT residue class. -/
theorem normalizedPairing_deficit (n m : ℕ) (hm : 0 < m) (hmem : qResidue m ∈ primorialStage n) :
    pError n - normalizedPairing n m =
      ∑' k : ℕ, positiveWeight k *
        ((1 - (((k % m : ℕ) : ℝ) / k)) * qSequence (qOne - pOptimizer n) k) :=
  matched_conductor_forcing_deficit (primorialStage n) (paretoStage n) m hm hmem
    ((toPareto_mem_stage_iff n _).mpr hmem)

theorem normalizedPairing_tail_bound (n m : ℕ) (hm : 0 < m)
    (hmem : qResidue m ∈ primorialStage n) :
    |pError n - normalizedPairing n m| ≤
      Real.sqrt (1 / (m : ℝ)) * ‖toPareto (tail (m - 1) (qOne - pOptimizer n))‖ :=
  matched_conductor_forcing_error (primorialStage n) (paretoStage n) m hm hmem
    ((toPareto_mem_stage_iff n _).mpr hmem)

theorem normalizedPairing_error_le (n m : ℕ) (hm : 0 < m)
    (hmem : qResidue m ∈ primorialStage n) :
    |pError n - normalizedPairing n m| ≤ Real.sqrt (1 / (m : ℝ)) := by
  have h := (normalizedPairing_tail_bound n m hm hmem).trans
    (mul_le_mul_of_nonneg_left (toPareto_tail_norm_le (m - 1) _) (Real.sqrt_nonneg _))
  have hn : ‖toPareto (qOne - pOptimizer n)‖ ≤ 1 := by
    have hpow := pError_le_one n
    change ‖toPareto (qOne - pOptimizer n)‖ ^ 2 ≤ 1 at hpow
    nlinarith [norm_nonneg (toPareto (qOne - pOptimizer n))]
  exact h.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg (1 / (m : ℝ))))

/-- No rate of convergence for the fitted vectors is required when the
conductor moves with the stage. -/
theorem normalizedPairing_tendsto (N m : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (hm : Tendsto m atTop atTop)
    (hmem : ∀ᶠ j in atTop, qResidue (m j) ∈ primorialStage (N j)) :
    Tendsto (fun j => normalizedPairing (N j) (m j)) atTop
      (𝓝 (‖toPareto pResidual‖ ^ 2)) := by
  have hp := hm.eventually (eventually_gt_atTop 0)
  have hmR : Tendsto (fun j => (m j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm
  have hinv : Tendsto (fun j => (1 : ℝ) / (m j : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hmR
  have hs : Tendsto (fun j => Real.sqrt (1 / (m j : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hinv
  have hz : Tendsto (fun j => pError (N j) - normalizedPairing (N j) (m j))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hs
    filter_upwards [hp, hmem] with j hj hjmem
    rw [Real.norm_eq_abs]
    exact normalizedPairing_error_le (N j) (m j) hj hjmem
  simpa only [Function.comp_def, sub_sub_cancel, sub_zero] using (pError_tendsto.comp hN).sub hz

/-- An included prime at every sufficiently late selected stage gives the
cofinal energy test of Proposition 3. -/
theorem normalizedPrimePairing_tendsto (N p : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (hp : Tendsto p atTop atTop)
    (hpn : ∀ᶠ j in atTop, (p j).Prime ∧ p j ≤ N j + 3) :
    Tendsto (fun j => normalizedPairing (N j) (p j)) atTop
      (𝓝 (‖toPareto pResidual‖ ^ 2)) := by
  apply normalizedPairing_tendsto N p hN hp
  filter_upwards [hpn] with j hj
  exact prime_mem (N j) (p j) hj.1 hj.2

/-- The whole primorial is itself a test conductor, with error at most the
inverse square root of the entire period. -/
theorem normalizedPeriodPairing_error_le (n : ℕ) :
    |pError n - normalizedPairing n (primorialPeriod n)| ≤
      Real.sqrt (1 / (primorialPeriod n : ℝ)) :=
  normalizedPairing_error_le n _ (primorialPeriod_pos n)
    (conductor_mem n _ ((by decide : 1 < 2).trans (primorialPeriod_gt_two n)) dvd_rfl)

theorem normalizedPeriodPairing_tendsto :
    Tendsto (fun n => normalizedPairing n (primorialPeriod n)) atTop
      (𝓝 (‖toPareto pResidual‖ ^ 2)) :=
  normalizedPairing_tendsto id primorialPeriod tendsto_id primorialPeriod_tendsto_atTop
    (Eventually.of_forall fun n =>
      conductor_mem n _ ((by decide : 1 < 2).trans (primorialPeriod_gt_two n)) dvd_rfl)

/-- A cofinal family with arbitrarily small upper bounds forces exact fit.
The family may use primes or the entire period. -/
theorem residual_zero_of_cofinal_normalizedPairing
    (N m : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hm : Tendsto m atTop atTop)
    (hmem : ∀ᶠ j in atTop, qResidue (m j) ∈ primorialStage (N j))
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ᶠ j in atTop, normalizedPairing (N j) (m j) ≤ ε) :
    ZetaTwoOptimizerStage.limitingResidual = 0 := by
  have hz : ‖toPareto pResidual‖ ^ 2 = 0 := by
    by_contra hn
    have hpos : 0 < ‖toPareto pResidual‖ ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn)
    have hlt : ‖toPareto pResidual‖ ^ 2 / 2 < ‖toPareto pResidual‖ ^ 2 := by linarith
    have he := (normalizedPairing_tendsto N m hN hm hmem).eventually (Ioi_mem_nhds hlt)
    obtain ⟨j, hj, hj'⟩ :=
      ((hbound (‖toPareto pResidual‖ ^ 2 / 2) (by positivity)).and_eventually he).exists
    exact (not_lt_of_ge hj) hj'
  have hP : pResidual = 0 := by
    apply paretoEquiv.injective
    change toPareto pResidual = toPareto (0 : QHilbert)
    rw [show toPareto (0 : QHilbert) = 0 from toParetoLinear.map_zero]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have hfit : qOne = pFit paretoSquarefreeClosure qOne := sub_eq_zero.mp hP
  exact sub_eq_zero.mpr ((exact_fit_iff _ _ toPareto_mem_paretoSquarefreeClosure_iff
    qOne).mpr hfit)

theorem riemannHypothesis_of_cofinal_normalizedPairing
    (N m : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hm : Tendsto m atTop atTop)
    (hmem : ∀ᶠ j in atTop, qResidue (m j) ∈ primorialStage (N j))
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ᶠ j in atTop, normalizedPairing (N j) (m j) ≤ ε) :
    RiemannHypothesis := by
  have hz := residual_zero_of_cofinal_normalizedPairing N m hN hm hmem hbound
  have h : qOne ∈ ZetaTwoOptimizerStage.closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hz).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr h)

/-- Complete metric gap on the primorial tower. -/
def metricGap (n : ℕ) : ℝ := zetaTwo * primorialError n - pError n

theorem metricGap_exact (n : ℕ) :
    metricGap n = ‖toPareto (stageDisplacement n)‖ ^ 2 +
      QParetoMetric.metricCorrection (qOne - primorialOptimizer n) := by
  have h := error_lower_identity (primorialStage n) (paretoStage n)
    (toPareto_mem_stage_iff n) qOne
  change zetaTwo * primorialError n = pError n + ‖toPareto (stageDisplacement n)‖ ^ 2 +
    QParetoMetric.metricCorrection (qOne - primorialOptimizer n) at h
  unfold metricGap
  linarith only [h]

theorem metricGap_pos (n : ℕ) : 0 < metricGap n := by
  have h := primorialError_pos n
  have hx : qOne ≠ qFit (primorialStage n) qOne := by
    intro he
    change qOne = primorialOptimizer n at he
    simp [primorialError, ← he] at h
  exact sub_pos.mpr (error_strict (primorialStage n) (paretoStage n)
    (toPareto_mem_stage_iff n) qOne hx)

theorem metricGap_tendsto :
    Tendsto metricGap atTop (𝓝 (zetaTwo * inner ℝ qOne witness)) := by
  have h : Tendsto metricGap atTop
      (𝓝 (zetaTwo * ‖ZetaTwoOptimizerStage.limitingResidual‖ ^ 2 - ‖toPareto pResidual‖ ^ 2)) := by
    unfold metricGap
    simpa only [ZetaTwoOptimizerStage.limitingResidual,
      QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure] using
      ((tendsto_const_nhds (x := zetaTwo)).mul primorialError_tendsto).sub pError_tendsto
  have he := error_lower_identity ZetaTwoOptimizerStage.closure paretoSquarefreeClosure
    toPareto_mem_paretoSquarefreeClosure_iff qOne
  change zetaTwo * ‖ZetaTwoOptimizerStage.limitingResidual‖ ^ 2 =
    ‖toPareto pResidual‖ ^ 2 + ‖toPareto displacement‖ ^ 2 +
      QParetoMetric.metricCorrection ZetaTwoOptimizerStage.limitingResidual at he
  have hmean : zetaTwo * ‖ZetaTwoOptimizerStage.limitingResidual‖ ^ 2 -
      ‖toPareto pResidual‖ ^ 2 = zetaTwo * inner ℝ qOne witness := by
    have hc := QParetoMetric.norm_identity ZetaTwoOptimizerStage.limitingResidual
    have hp := pareto_inner_identity ZetaTwoOptimizerStage.limitingResidual
      ZetaTwoOptimizerStage.limitingResidual
    simp only [real_inner_self_eq_norm_sq] at hp
    rw [mul_sub] at hp
    rw [witness_mean_energy]
    linarith only [he, hc, hp]
  rw [← hmean]
  exact h

/-- Cofinal smallness of the actual complete metric gap forces the witness
mean and the squarefree Q residual to vanish. -/
theorem residual_zero_of_cofinal_metricGap
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, metricGap n ≤ ε) :
    ZetaTwoOptimizerStage.limitingResidual = 0 := by
  have hnonneg : 0 ≤ zetaTwo * inner ℝ qOne witness := by
    rw [witness_mean_energy]
    exact add_nonneg (mul_nonneg zetaTwo_pos.le (B_positive _)) (sq_nonneg _)
  have hz : zetaTwo * inner ℝ qOne witness = 0 := by
    apply le_antisymm _ hnonneg
    by_contra! hp
    have hh : zetaTwo * inner ℝ qOne witness / 2 < zetaTwo * inner ℝ qOne witness := by linarith
    have he := metricGap_tendsto.eventually (Ioi_mem_nhds hh)
    obtain ⟨n, hn, hn'⟩ :=
      ((h (zetaTwo * inner ℝ qOne witness / 2) (by positivity)).and_eventually he).exists
    exact (not_lt_of_ge hn) hn'
  exact residual_eq_zero_of_witness_mean_zero ((mul_eq_zero.mp hz).resolve_left zetaTwo_pos.ne')

end RiemannResearch.RH.QPrimorialMatchedDisplacement
