/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusSublinearEnergy
import RiemannResearch.RH.ParetoSublinearResidualTail
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Reciprocal Möbius convergence supplies ordinary cancellation

The exact finite summation-by-parts identity is
`M(N) = N * m(N) - ∑ k < N, m(k)`, where `m(0) = 0`.
Cesàro convergence therefore supplies the ordinary cancellation premise
from convergence of the reciprocal sums. In particular, the canonical
sublinear-energy theorem needs only the one arithmetic provider `m(N) → 0`.
That provider is retained as an explicit hypothesis; no PNT theorem is asserted.

Source: the user-provided direct Pareto approximation manuscript, Section 3,
for the two arithmetic inputs being compared. The reduction uses elementary
finite summation by parts and Mathlib's Cesàro convergence theorem.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

/-- The reciprocal Möbius sum acquires exactly its new final term. -/
theorem mobiusReciprocalSum_succ (N : ℕ) :
    mobiusReciprocalSum (N + 1) = mobiusReciprocalSum N +
      (ArithmeticFunction.moebius (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  unfold mobiusReciprocalSum
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- Exact finite summation by parts, retaining the terminal correction. -/
theorem mobius_sum_eq_reciprocal_sub_cesaro_numerator (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)) =
      (N : ℝ) * mobiusReciprocalSum N -
        ∑ k ∈ Finset.range N, mobiusReciprocalSum k := by
  induction N with
  | zero => simp [mobiusReciprocalSum]
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ,
      mobiusReciprocalSum_succ, ih]
    push_cast
    have hc : ((N : ℝ) + 1) *
        ((ArithmeticFunction.moebius (N + 1) : ℝ) / ((N : ℝ) + 1)) =
          (ArithmeticFunction.moebius (N + 1) : ℝ) := by
      have hden : (N : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
      field_simp
    nlinarith [hc]

/-- The ordinary normalized sum is the reciprocal sum minus its Cesàro mean. -/
theorem mobius_sum_div_eq_reciprocal_sub_cesaro (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)) / (N : ℝ) =
      mobiusReciprocalSum N -
        (N⁻¹ : ℝ) * ∑ k ∈ Finset.range N, mobiusReciprocalSum k := by
  by_cases hN : N = 0
  · simp [hN, mobiusReciprocalSum]
  · have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    rw [mobius_sum_eq_reciprocal_sub_cesaro_numerator]
    field_simp

/-- Convergence of the reciprocal sums, to any finite limit, forces ordinary
Möbius cancellation. This is only the easy Cesàro direction. -/
theorem mobius_sum_div_tendsto_zero_of_reciprocal_tendsto
    {L : ℝ} (hm : Tendsto mobiusReciprocalSum atTop (𝓝 L)) :
    Tendsto (fun N : ℕ =>
      (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)) / (N : ℝ))
      atTop (𝓝 0) := by
  have heq : (fun N : ℕ =>
      (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)) / (N : ℝ)) =
      (fun N : ℕ => mobiusReciprocalSum N -
        (N⁻¹ : ℝ) * ∑ k ∈ Finset.range N, mobiusReciprocalSum k) :=
    funext mobius_sum_div_eq_reciprocal_sub_cesaro
  rw [heq]
  simpa only [sub_self] using hm.sub hm.cesaro

/-- The canonical full-energy result needs only reciprocal Möbius cancellation;
the ordinary cancellation premise follows by the exact Cesàro identity. -/
theorem canonicalMobiusHilbert_sublinear_of_reciprocal_cancellation
    (hm : Tendsto mobiusReciprocalSum atTop (𝓝 0)) :
    Tendsto (fun N => ‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ))
      atTop (𝓝 0) :=
  canonicalMobiusHilbert_sublinear_of_mobius_cancellation
    (mobius_sum_div_tendsto_zero_of_reciprocal_tendsto hm) hm

namespace CoefficientStabilization

/-- Conditional research reduction with just one arithmetic provider. The
bounded cofinal normalized residual-tail estimate is still open. -/
theorem riemannHypothesis_of_reciprocal_cancellation_and_bounded_tail
    (hm : Tendsto mobiusReciprocalSum atTop (𝓝 0))
    (C : ℝ) (hbounded : ∃ᶠ N : ℕ in atTop, (N : ℝ) * residualTailEnergy N ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_mobius_cancellation_and_bounded_tail
    (mobius_sum_div_tendsto_zero_of_reciprocal_tendsto hm) hm C hbounded

end CoefficientStabilization
end RiemannResearch.RH.Pareto
