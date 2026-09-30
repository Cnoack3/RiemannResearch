/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoFirstSitePrimeAlignment
import RiemannResearch.RH.BaezDuarteNaturalApproximation

/-!
# RH consequences for the complete first-site budget

Source: Luis Báez-Duarte, A strengthening of the Nyman--Beurling criterion
for the Riemann hypothesis, Theorem 1.1, arXiv:math/0205003.
The cited theorem supports the external RH-to-NaturalApproximation direction.
Its analytic proof is not imported as an axiom: the existing explicit
hBaezDuarte hypothesis is retained. The natural/centered/Pareto transfer,
first-point closure equivalence and capacity conversion are Lean-proved.
The unconditional capacity-to-RH direction needs no hBaezDuarte.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.RH.Pareto.BaezDuarte

theorem tailCapacity_tendsto_of_naturalApproximation
    (h : NaturalApproximation) : Tendsto tailCapacity atTop atTop := by
  apply tailCapacity_tendsto_iff.mpr
  change Tendsto (walkError residueAtom id (paretoPointHilbert 0)) atTop (𝓝 0)
  apply (walkError_tendsto_zero_iff residueAtom id Function.surjective_id (paretoPointHilbert 0)).mpr
  exact firstPoint_mem_iff_one_mem.mpr (naturalApproximation_iff_one_mem.mp h)

/-- Conditional on the classical analytic RH-to-approximation provider,
RH implies divergence of the complete first-site capacity. -/
theorem tailCapacity_tendsto_of_RH
    (hBaezDuarte : RiemannHypothesis → NaturalApproximation)
    (hRH : RiemannHypothesis) : Tendsto tailCapacity atTop atTop :=
  tailCapacity_tendsto_of_naturalApproximation (hBaezDuarte hRH)

/-- An exact RH equivalence with its sole external analytic provider explicit. -/
theorem RH_iff_tailCapacity_tendsto
    (hBaezDuarte : RiemannHypothesis → NaturalApproximation) :
    RiemannHypothesis ↔ Tendsto tailCapacity atTop atTop :=
  ⟨tailCapacity_tendsto_of_RH hBaezDuarte,
    riemannHypothesis_of_tailCapacity_tendsto⟩

theorem RH_iff_prime_alignment_unbounded
    (hBaezDuarte : RiemannHypothesis → NaturalApproximation) :
    RiemannHypothesis ↔
      ∀ B : ℝ, ∃ N : ℕ, 0 < N ∧
        B < primeMeanMismatchBudget N + primeCancellationVariance N +
          compositeGainBudget N :=
  (RH_iff_tailCapacity_tendsto hBaezDuarte).trans
    tailCapacity_tendsto_iff_prime_alignment_unbounded

/-- Small capacity relative to the source forces normalized signed cancellation,
even if the capacity itself diverges. This hypothesis is not supplied here. -/
theorem primeSignedBudget_ratio_tendsto_of_capacity_sublinear_source
    (h : Tendsto (fun N => tailCapacity (N + 1) / primeSourceBudget N)
      atTop (𝓝 0)) :
    Tendsto (fun N => primeSignedBudget N / primeSourceBudget N)
      atTop (𝓝 (-1 : ℝ)) := by
  have hi := tendsto_inv_atTop_zero.comp primeSourceBudget_tendsto
  have hc : Tendsto (fun N => tailCapacity 1 / primeSourceBudget N) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := tailCapacity 1)).mul hi
  have ht : Tendsto (fun N => tailCapacity (N + 1) / primeSourceBudget N -
      tailCapacity 1 / primeSourceBudget N - 1) atTop (𝓝 (-1 : ℝ)) := by
    simpa using (h.sub hc).sub (tendsto_const_nhds (x := (1 : ℝ)))
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [capacity_eq_prime_signed_budget N]
  field_simp [ne_of_gt (primeSourceBudget_pos N hN)]
  ring

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
