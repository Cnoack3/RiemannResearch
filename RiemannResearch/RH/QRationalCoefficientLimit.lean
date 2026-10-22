/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalMinimizerConvergence
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.SquarefreeStageExhaustion
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Topology.Algebra.Module.Basic
import Lean.Elab.Tactic.Omega

/-!
# Actual rational divisor coefficients stabilize

Source: the user-directed squarefree-closure dependency continuation,
20 October 2026. The continuous coefficient theory is reused from
`SquarefreeMobiusProjection`; norm convergence is reused from
`QRationalMinimizerConvergence`.

The selected normal-equation coefficients are arbitrary outside the finite
conductor set, and the zero atom at conductor one is redundant. For each
fixed squarefree conductor at least two, eventual primorial inclusion makes
its actual selected coefficient equal to the continuous coefficient map.
Thus it converges unconditionally to the coefficient of the legal projection.
Identifying all these limits with minus Moebius remains exactly the constant
closure obligation; no arithmetic identification of the limits is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QRationalCoprimeTail
open ZetaTwoHilbert ZetaTwoProbability QSquarefreePrimorialCofinality SquarefreeMobiusProjection
open Pareto.SquarefreeStageExhaustion

/-- The continuous coefficient map extracts each nonredundant coefficient
from the actual full finite divisor synthesis. -/
theorem qCoefficientCLM_qDivisorFit (L m : ℕ) (hL : 0 < L) (hm : 2 ≤ m)
    (c : ℕ → ℝ) :
    qCoefficientCLM m (qDivisorFit L c) =
      if m ∈ L.divisors then c m else 0 := by
  classical
  have hpair (d : ℕ) (hd : d ∈ L.divisors) :
      qCoefficientCLM m (qResidue d) = if m = d then 1 else 0 := by
    by_cases hd1 : d = 1
    · simp [hd1, show m ≠ 1 by omega]
    · have hd0 : d ≠ 0 := by
        intro hz
        subst d
        exact (ne_of_gt hL) (Nat.eq_zero_of_zero_dvd (Nat.dvd_of_mem_divisors hd))
      have hd2 : 2 ≤ d := by omega
      have hm' : m - 2 + 2 = m := by omega
      have hd' : d - 2 + 2 = d := by omega
      have he : m - 2 = d - 2 ↔ m = d := by omega
      simpa only [hm', hd', he] using q_coordinate_biorthogonal (m - 2) (d - 2)
  calc
    qCoefficientCLM m (qDivisorFit L c) =
        ∑ d ∈ L.divisors, c d * (if m = d then 1 else 0) := by
      simp only [qDivisorFit, map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [hpair d hd]
    _ = if m ∈ L.divisors then c m else 0 := by
      simp [mul_ite]

/-- Outside the finite dictionary the chosen coefficients have no invariant
meaning. Eventual divisibility removes this ambiguity at every fixed legal
squarefree conductor. -/
theorem rationalCoefficients_eventually_eq_coordinate (m : ℕ) (hm : 2 ≤ m)
    (hsf : Squarefree m) :
    ∀ᶠ n in atTop, rationalCoefficients (primorialPeriod n) m =
      qCoefficientCLM m (rationalMinimizer (primorialPeriod n)) := by
  filter_upwards [eventually_ge_atTop m] with n hn
  have hmem : m ∈ (primorialPeriod n).divisors :=
    Nat.mem_divisors.mpr ⟨squarefree_dvd_primorialPeriod m n hsf hn,
      ne_of_gt (primorialPeriod_pos n)⟩
  symm
  change qCoefficientCLM m
    (qDivisorFit (primorialPeriod n) (rationalCoefficients (primorialPeriod n))) = _
  rw [qCoefficientCLM_qDivisorFit _ _ (primorialPeriod_pos n) hm, if_pos hmem]

/-- Every genuine rational optimizer coefficient at a fixed legal conductor
has the same limit as the complete-Q orthogonal projection coefficient. -/
theorem rationalCoefficients_tendsto (m : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m) :
    Tendsto (fun n => rationalCoefficients (primorialPeriod n) m) atTop
      (𝓝 (qLimitCoefficient m)) := by
  have ht : Tendsto
      (fun n => qCoefficientCLM m (rationalMinimizer (primorialPeriod n))) atTop
      (𝓝 (qLimitCoefficient m)) := by
    have hc := (qCoefficientCLM m).continuous.tendsto
      (qSquarefreeCRTSpan.topologicalClosure.starProjection qOne)
    simpa only [Function.comp_def, qLimitCoefficient,
      QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure] using
      hc.comp rationalMinimizer_tendsto
  apply ht.congr'
  filter_upwards [rationalCoefficients_eventually_eq_coordinate m hm hsf] with n hn
  exact hn.symm

/-- Actual rational normal-equation coefficients tend simultaneously to
minus Moebius exactly when the constant lies in the squarefree legal closure.
The limiting-value assertion remains the arithmetic obligation. -/
theorem rationalCoefficients_tendsto_moebius_iff :
    (∀ m : ℕ, 2 ≤ m → Squarefree m →
      Tendsto (fun n => rationalCoefficients (primorialPeriod n) m) atTop
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔
      qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  constructor
  · intro h
    have hlimit : ∀ i : ℕ, Squarefree (i + 2) →
        qLimitCoefficient (i + 2) = -(ArithmeticFunction.moebius (i + 2) : ℝ) := by
      intro i hi
      exact tendsto_nhds_unique
        (rationalCoefficients_tendsto (i + 2) (by omega) hi)
        (h (i + 2) (by omega) hi)
    have hmem := q_coefficient_limits_iff_closure.mp
      (q_limit_values_iff_coefficient_limits.mp hlimit)
    simpa only [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure] using hmem
  · intro hmem m hm hsf
    have ht := rationalMinimizer_tendsto_qOne_iff.mpr hmem
    have hc := ((qCoefficientCLM m).continuous.tendsto qOne).comp ht
    rw [q_target_coordinate m (by omega)] at hc
    apply hc.congr'
    filter_upwards [rationalCoefficients_eventually_eq_coordinate m hm hsf] with n hn
    exact hn.symm

end RiemannResearch.RH.QRationalCoprimeTail
