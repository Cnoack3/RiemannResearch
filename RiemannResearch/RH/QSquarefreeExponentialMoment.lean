/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QExponentialMoment
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.QSquarefreeLogResidualTail
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QSquarefreeCapacity

/-!
# Exponential-moment dichotomy for the actual squarefree correction

Source: the user's prime-resampling research agenda. A positive exponential
moment implies a logarithmic physical envelope, which contradicts the existing
tail dichotomy unless the actual squarefree residual vanishes. Finiteness of
the moment is an Open arithmetic obligation, not an unconditional estimate.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreeExponentialMoment
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeSmoothedProjection
open QExponentialMoment QPolylogTailEnergy QSquarefreeLogResidualTail

/-- A single finite positive exponential moment of the actual limiting
correction forces the squarefree residual to vanish. The moment is the
remaining arithmetic hypothesis, not an asserted unconditional bound. -/
theorem residual_zero_of_correction_exponentialMoment_summable
    (κ : ℝ) (hκ : 0 < κ)
    (hs : Summable (fun n : ℕ =>
      positiveQWeight n * Real.exp (κ * |qSequence correction n|))) :
    limitingResidual = 0 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_log_envelope_of_sequence_exponentialMoment_summable
      (qSequence correction) (by simp) κ hκ hs
  obtain ⟨D, hD⟩ := exists_log_scaled_tail_bound_of_polylog correction 1 C hC
    (by simpa only [pow_one] using hbound)
  apply (residual_zero_iff_correction_frequently_bounded_log_scaled_tail 4).mpr
  refine ⟨D, (Eventually.of_forall ?_).frequently⟩
  intro N
  exact hD N

/-- For the actual correction, positive exponential moment finiteness is
equivalent to zero residual. General QHilbert vectors do not satisfy this
dichotomy; its forward implication is supplied by the arithmetic tail theorem. -/
theorem correction_exponentialMoment_summable_iff_residual_zero
    (κ : ℝ) (hκ : 0 < κ) :
    Summable (fun n : ℕ =>
      positiveQWeight n * Real.exp (κ * |qSequence correction n|)) ↔
      limitingResidual = 0 := by
  constructor
  · exact residual_zero_of_correction_exponentialMoment_summable κ hκ
  · intro hr
    have hc : correction = 0 := by simp [correction, hr]
    have hq : qSequence (0 : QHilbert) = 0 := qSequenceLinear.map_zero
    simpa [hc, hq] using positiveQWeight_summable

/-- Conditional RH consumer with exactly the finite exponential moment
premise displayed in its declaration. -/
theorem riemannHypothesis_of_correction_exponentialMoment_summable
    (κ : ℝ) (hκ : 0 < κ)
    (hs : Summable (fun n : ℕ =>
      positiveQWeight n * Real.exp (κ * |qSequence correction n|))) :
    RiemannHypothesis := by
  have hr := residual_zero_of_correction_exponentialMoment_summable κ hκ hs
  have hm : qOne ∈ closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

theorem movingExponentialAtom_tendsto (κ : ℝ) (n : ℕ) :
    Tendsto
      (fun N => positiveQWeight n *
        Real.exp (κ * |qSequence (movingCorrection N) n|)) atTop
      (𝓝 (positiveQWeight n * Real.exp (κ * |qSequence correction n|))) := by
  exact ((Real.continuous_exp.tendsto _).comp
    ((qSequence_tendsto_of_tendsto movingCorrection_tendsto n).abs.const_mul κ)).const_mul
      (positiveQWeight n)

theorem movingExponentialFiniteSum_tendsto (κ : ℝ) (S : Finset ℕ) :
    Tendsto
      (fun N => ∑ n ∈ S, positiveQWeight n *
        Real.exp (κ * |qSequence (movingCorrection N) n|)) atTop
      (𝓝 (∑ n ∈ S, positiveQWeight n * Real.exp (κ * |qSequence correction n|))) := by
  exact tendsto_finsetSum S (fun n _ => movingExponentialAtom_tendsto κ n)

/-- Good stages may depend on the tested finite set. Only one common finite
moment budget is required, and complete-stage moments need not be estimated. -/
theorem correction_exponentialMoment_summable_of_frequently_finiteSum_bound
    (κ M : ℝ)
    (hM : ∀ S : Finset ℕ, ∃ᶠ N in atTop,
      (∑ n ∈ S, positiveQWeight n *
        Real.exp (κ * |qSequence (movingCorrection N) n|)) ≤ M) :
    Summable (fun n : ℕ =>
      positiveQWeight n * Real.exp (κ * |qSequence correction n|)) := by
  apply summable_of_sum_le (c := M)
    (fun n => mul_nonneg (positiveQWeight_nonneg n) (Real.exp_pos _).le)
  intro S
  by_contra h
  have hg := (movingExponentialFiniteSum_tendsto κ S).eventually
    (Ioi_mem_nhds (lt_of_not_ge h))
  obtain ⟨N, hN, hgt⟩ := ((hM S).and_eventually hg).exists
  exact (not_lt_of_ge hN) hgt

/-- Exact finite-test criterion. Necessity uses budget two because every
finite set has Q mass at most one. Sufficiency uses only the common budget. -/
theorem residual_zero_iff_frequently_exponential_finiteSum_bound
    (κ : ℝ) (hκ : 0 < κ) :
    limitingResidual = 0 ↔ ∃ M : ℝ, ∀ S : Finset ℕ, ∃ᶠ N in atTop,
      (∑ n ∈ S, positiveQWeight n *
        Real.exp (κ * |qSequence (movingCorrection N) n|)) ≤ M := by
  constructor
  · intro hr
    refine ⟨2, ?_⟩
    intro S
    have hc : correction = 0 := by simp [correction, hr]
    have hq : qSequence (0 : QHilbert) = 0 := qSequenceLinear.map_zero
    have hle : (∑ n ∈ S, positiveQWeight n) ≤ 1 := by
      simpa only [positiveQWeight_tsum] using
        positiveQWeight_summable.sum_le_tsum S (fun n _ => positiveQWeight_nonneg n)
    have hlim : (∑ n ∈ S,
        positiveQWeight n * Real.exp (κ * |qSequence correction n|)) < 2 := by
      simp only [hc, hq, Pi.zero_apply, abs_zero, mul_zero, Real.exp_zero, mul_one]
      linarith
    exact ((movingExponentialFiniteSum_tendsto κ S).eventually
      (Iio_mem_nhds hlim)).frequently.mono (fun N hN => hN.le)
  · rintro ⟨M, hM⟩
    exact residual_zero_of_correction_exponentialMoment_summable κ hκ
      (correction_exponentialMoment_summable_of_frequently_finiteSum_bound κ M hM)

theorem riemannHypothesis_of_frequently_exponential_finiteSum_bound
    (κ M : ℝ) (hκ : 0 < κ)
    (hM : ∀ S : Finset ℕ, ∃ᶠ N in atTop,
      (∑ n ∈ S, positiveQWeight n *
        Real.exp (κ * |qSequence (movingCorrection N) n|)) ≤ M) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_correction_exponentialMoment_summable κ hκ
    (correction_exponentialMoment_summable_of_frequently_finiteSum_bound κ M hM)

/-- Any positive stretched exponential moment suffices, however small its exponent.
Its finiteness is still an Open arithmetic obligation for the actual correction. -/
theorem residual_zero_of_correction_stretchedExponentialMoment_summable
    (α κ : ℝ) (hα : 0 < α) (hκ : 0 < κ)
    (hs : Summable (fun n : ℕ => positiveQWeight n *
      Real.exp (κ * (|qSequence correction n| ^ α)))) :
    limitingResidual = 0 := by
  obtain ⟨m, D, hD, hbound⟩ :=
    exists_polylog_envelope_of_stretchedExponentialMoment_summable correction α κ hα hκ hs
  obtain ⟨M, hM⟩ := exists_log_scaled_tail_bound_of_polylog correction m D hD hbound
  exact (residual_zero_iff_correction_frequently_bounded_log_scaled_tail (2 * m + 2)).mpr
    ⟨M, (Eventually.of_forall hM).frequently⟩

theorem correction_stretchedExponentialMoment_summable_iff_residual_zero
    (α κ : ℝ) (hα : 0 < α) (hκ : 0 < κ) :
    Summable (fun n : ℕ => positiveQWeight n *
      Real.exp (κ * (|qSequence correction n| ^ α))) ↔ limitingResidual = 0 := by
  constructor
  · exact residual_zero_of_correction_stretchedExponentialMoment_summable α κ hα hκ
  · intro hr
    have hc : correction = 0 := by simp [correction, hr]
    have hq : qSequence (0 : QHilbert) = 0 := qSequenceLinear.map_zero
    simpa [hc, hq, Real.zero_rpow hα.ne'] using positiveQWeight_summable

theorem riemannHypothesis_of_correction_stretchedExponentialMoment_summable
    (α κ : ℝ) (hα : 0 < α) (hκ : 0 < κ)
    (hs : Summable (fun n : ℕ => positiveQWeight n *
      Real.exp (κ * (|qSequence correction n| ^ α)))) :
    RiemannHypothesis := by
  have hr := residual_zero_of_correction_stretchedExponentialMoment_summable α κ hα hκ hs
  have hm : qOne ∈ closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

end RiemannResearch.RH.QSquarefreeExponentialMoment
