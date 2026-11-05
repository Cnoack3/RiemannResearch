/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QFiniteEighthMoment
import RiemannResearch.RH.ParetoNymanNorm
import RiemannResearch.RH.ZetaTwoTargetFirstMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # The physical eighth-moment criterion with Lee's explicit arithmetic input

J. Lee, *Convergence and the Riemann hypothesis*, Comm. Korean Math. Soc.
11 (1996), 57–62. The centered natural sums and their convergence below the
zero-free exponent are described by L. Báez-Duarte, https://arxiv.org/abs/math/0011254,
§1, (1.12), (1.17). The integral below is the powered L^(8/7) error of exactly
those sums. We identify it with the complete Pareto moment and transfer it to
Q with the original finite squarefree competitors. The deduction of the
vanishing integral from a fixed zero-free half-plane is an external input.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement

open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage

/-- Lee's centered natural Möbius sums, with Lebesgue measure on `(0,1]`.
The sign gives the error against `1` for the negative Möbius approximant. -/
def leeUnitMoment (M : ℕ) : ℝ≥0∞ :=
  ∫⁻ u : ℝ in Ioc 0 1, ENNReal.ofReal (|1 + ∑ m ∈ Finset.Icc 1 M,
    (ArithmeticFunction.moebius m : ℝ) * (Int.fract (1 / ((m : ℝ) * u)) -
      (1 / (m : ℝ)) * Int.fract (1 / u))| ^ (8 / 7 : ℝ))

/-- The discrete moment at raw Möbius cutoff `M`, over all physical sites. -/
def leeParetoMoment (M : ℕ) : ℝ :=
  ∑' k, positiveWeight k * |ZetaTwoMobiusFloor.residual M k| ^ (8 / 7 : ℝ)

private theorem leeParetoMoment_summable (M : ℕ) (hM : 0 < M) :
    Summable (fun k => positiveWeight k * |ZetaTwoMobiusFloor.residual M k| ^ (8 / 7 : ℝ)) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveWeight_nonneg k) (Real.rpow_nonneg (abs_nonneg _) _)) _
    (positiveWeight_summable.mul_right ((M : ℝ) ^ (8 / 7 : ℝ)))
  intro k
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (abs_nonneg _) (ZetaTwoMobiusFloor.residual_abs_le M k hM) (by norm_num))
    (positiveWeight_nonneg k)

private theorem leeParetoMoment_nonneg (M : ℕ) : 0 ≤ leeParetoMoment M :=
  tsum_nonneg fun k => mul_nonneg (positiveWeight_nonneg k) (Real.rpow_nonneg (abs_nonneg _) _)

/-- Exact conversion of Lee's integral, including its full tail and all Möbius signs. -/
theorem leeUnitMoment_eq_paretoMoment (M : ℕ) (hM : 0 < M) :
    leeUnitMoment M = ENNReal.ofReal (leeParetoMoment M) := by
  unfold leeUnitMoment
  calc
    _ = ∫⁻ u, ENNReal.ofReal (|ZetaTwoMobiusFloor.residual M (reciprocalFloor u)| ^
          (8 / 7 : ℝ)) ∂uniformUnit := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hsum : (∑ m ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius m : ℝ) *
          (Int.fract (1 / ((m : ℝ) * u)) - (1 / (m : ℝ)) * Int.fract (1 / u))) =
          ∑ m ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius m : ℝ) *
            ArithmeticCumulative.residueFraction m (reciprocalFloor u) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact congrArg (fun v : ℝ => (ArithmeticFunction.moebius m : ℝ) * v)
          (pareto_nyman_pointwise u hu.1 m (Finset.mem_Icc.mp hm).1)
      simp only [ZetaTwoMobiusFloor.residual, hsum]
    _ = _ := by
      rw [uniformUnit_lintegral_reciprocalFloor (fun k =>
        ENNReal.ofReal (|ZetaTwoMobiusFloor.residual M k| ^ (8 / 7 : ℝ)))]
      unfold leeParetoMoment
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (positiveWeight_nonneg k)
        (Real.rpow_nonneg (abs_nonneg _) _)) (leeParetoMoment_summable M hM)]
      apply tsum_congr
      intro k
      rw [ENNReal.ofReal_mul (positiveWeight_nonneg k)]
      exact mul_comm _ _

/-- The concrete finite Lee witnesses suffice under convergence of their Pareto moments.
Our stage `N` includes conductors up to `N+1`. -/
theorem hasSubcriticalApproximation_of_lee_pareto_moment
    (hLee : Tendsto (fun N : ℕ => leeParetoMoment (N + 1)) atTop (𝓝 0)) :
    HasSubcriticalApproximation := by
  let qTerm (N k : ℕ) : ℝ :=
    positiveQWeight k * |qSequence (qOne - mobiusTrial N) k| ^ (8 / 7 : ℝ)
  have hterm0 (N k : ℕ) : 0 ≤ qTerm N k :=
    mul_nonneg (positiveQWeight_nonneg k) (Real.rpow_nonneg (abs_nonneg _) _)
  have hterm (N k : ℕ) : qTerm N k ≤ (2 / zetaTwo) *
      (positiveWeight k * |ZetaTwoMobiusFloor.residual (N + 1) k| ^ (8 / 7 : ℝ)) := by
    by_cases hk : k = 0
    · simp [qTerm, hk, positiveWeight, positiveQWeight]
    · have hweight : positiveQWeight k ≤ (2 / zetaTwo) * positiveWeight k := by
        rw [show (2 / zetaTwo) * positiveWeight k = (2 * positiveWeight k) / zetaTwo by ring]
        exact (le_div_iff₀ zetaTwo_pos).2 (by
          simpa only [mul_comm (positiveQWeight k) zetaTwo] using
            ZetaTwoParetoTransfer.zetaTwo_mul_QWeight_le_two_mul_paretoWeight k)
      dsimp only [qTerm]
      rw [qSequence_mobiusResidual N k (Nat.pos_of_ne_zero hk), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hweight (Real.rpow_nonneg (abs_nonneg _) _)
  have hs (N : ℕ) : Summable (qTerm N) :=
    Summable.of_nonneg_of_le (hterm0 N) (hterm N)
      ((leeParetoMoment_summable (N + 1) (Nat.succ_pos N)).mul_left (2 / zetaTwo))
  have hle (N : ℕ) : (∑' k, qTerm N k) ≤ (2 / zetaTwo) * leeParetoMoment (N + 1) := by
    have h := (hs N).tsum_le_tsum (hterm N)
      ((leeParetoMoment_summable (N + 1) (Nat.succ_pos N)).mul_left (2 / zetaTwo))
    simpa only [tsum_mul_left, leeParetoMoment] using h
  have hq : Tendsto (fun N => ∑' k, qTerm N k) atTop (𝓝 0) := by
    apply squeeze_zero (fun N => tsum_nonneg (hterm0 N)) hle
    simpa only [mul_zero] using hLee.const_mul (2 / zetaTwo)
  refine ⟨mobiusTrial, ?_, hs, ?_⟩
  · intro N
    exact (Submodule.span ℝ (Set.range squarefreeAtom)).le_topologicalClosure
      (RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_le squarefreeAtom id N
        (ZetaTwoTargetFirstMoment.mobiusTrial_mem_stage N))
  · exact hq.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 7 / 8)

/-- Lee's published subcritical estimate, in its own continuous normalization,
provides precisely the analytic premise of the physical criterion. -/
theorem hasSubcriticalApproximation_of_lee_unit_moment
    (hLee : Tendsto leeUnitMoment atTop (𝓝 0)) : HasSubcriticalApproximation := by
  apply hasSubcriticalApproximation_of_lee_pareto_moment
  have h := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
    (hLee.comp (tendsto_add_atTop_nat 1))
  change Tendsto (fun N : ℕ => (leeUnitMoment (N + 1)).toReal) atTop (𝓝 (ENNReal.toReal 0)) at h
  have he (N : ℕ) : (leeUnitMoment (N + 1)).toReal = leeParetoMoment (N + 1) := by
    rw [leeUnitMoment_eq_paretoMoment _ (Nat.succ_pos N), ENNReal.toReal_ofReal
      (leeParetoMoment_nonneg _)]
  simpa only [he, ENNReal.toReal_zero] using h

/-- The aligned finite-head test with its only arithmetic input stated as a
limit of the original, complete Lebesgue integrals of Lee's approximants. -/
theorem riemannHypothesis_of_lee_unit_and_finite_eighth_liminf
    (hLee : Tendsto leeUnitMoment atTop (𝓝 0))
    (h : liminf (fun N : ℕ =>
      (Real.nnabs (eighthHead (finiteDisplacement N) N) : ℝ≥0∞)) atTop < ⊤) :
    RiemannHypothesis :=
  riemannHypothesis_of_finite_eighth_liminf (hasSubcriticalApproximation_of_lee_unit_moment hLee) h

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
