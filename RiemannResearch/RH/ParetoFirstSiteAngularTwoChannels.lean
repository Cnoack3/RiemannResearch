/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoFirstSitePrimeAngular
import RiemannResearch.Analysis.VanishingRegressionSlope

/-!
# Vanishing survivor slope and the two gain channels

Source: fixed finite-head limiting argument and exact weighted regression.
The capacity/source rate motivated by Burnol and PNT remains explicit.
The full screened determinant, historical slope and every nonprime gain remain.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.WeightedScalarEnergy
open RiemannResearch.RH.Pareto.IntegerDPP

def primeSurvivorSlope (N : ℕ) : ℝ :=
  (primeSourceBudget N + primeCrossBudget N) / primeSourceBudget N

theorem primeCancellationVariance_eq_survivor_square (N : ℕ) :
    primeCancellationVariance N =
      square (Finset.range N) primeSchurWeight
        (fun n => schurEta (n + 1) - primeSurvivorSlope N * factorialPrimeDelta n) := by
  have he := centered_square_eq_sub_quotient (Finset.range N) primeSchurWeight
    factorialPrimeDelta (fun n => schurEta (n + 1))
  rw [← primeGainBudget_eq_weighted, ← primeSourceBudget_eq_weighted,
    ← prime_source_add_cross_eq_survivor] at he
  change _ = primeGainBudget N - primeMeanMismatchBudget N at he
  have hex : primeGainBudget N - primeMeanMismatchBudget N =
      primeCancellationVariance N := by linarith [primeGainBudget_eq_alignment N]
  exact (he.trans hex).symm

theorem primeGainBudget_le_angular_tsum
    (ht : Tendsto primeSurvivorSlope atTop (𝓝 0))
    (hA : Summable primeAngularInnovation) (M : ℕ) :
    primeGainBudget M ≤ ∑' n, primeAngularInnovation n := by
  rw [primeGainBudget_eq_weighted]
  apply square_le_of_bounded_centered_prefixes primeSchurWeight factorialPrimeDelta
    (fun n => schurEta (n + 1)) primeSurvivorSlope primeSchurWeight_nonneg ht
  intro N
  rw [← primeCancellationVariance_eq_survivor_square, primeCancellationVariance_eq_sum]
  exact hA.sum_le_tsum (Finset.range N) (fun n _ => primeAngularInnovation_nonneg n)

/-- The historical mean is bounded by the remaining angular mass. -/
theorem primeMeanMismatchBudget_le_angular_tail
    (ht : Tendsto primeSurvivorSlope atTop (𝓝 0))
    (hA : Summable primeAngularInnovation) (N : ℕ) :
    primeMeanMismatchBudget N ≤
      (∑' n, primeAngularInnovation n) -
        ∑ n ∈ Finset.range N, primeAngularInnovation n := by
  have hb := primeGainBudget_le_angular_tsum ht hA N
  rw [primeGainBudget_eq_alignment, primeCancellationVariance_eq_sum] at hb
  linarith

theorem factorialPrimeGain_summable_of_angular_of_slope_zero
    (ht : Tendsto primeSurvivorSlope atTop (𝓝 0))
    (hA : Summable primeAngularInnovation) : Summable factorialPrimeGain := by
  apply summable_of_sum_range_le factorialPrimeGain_nonneg
  intro N
  exact primeGainBudget_le_angular_tsum ht hA N

theorem primeAngularInnovation_summable_of_gain
    (hG : Summable factorialPrimeGain) : Summable primeAngularInnovation := by
  apply summable_of_sum_range_le primeAngularInnovation_nonneg
  intro N
  have hg : primeGainBudget N ≤ ∑' n, factorialPrimeGain n :=
    hG.sum_le_tsum (Finset.range N) (fun n _ => factorialPrimeGain_nonneg n)
  rw [primeGainBudget_eq_alignment, primeCancellationVariance_eq_sum] at hg
  linarith [primeMeanMismatchBudget_nonneg N]

theorem primeAngularInnovation_summable_iff_gain_of_slope_zero
    (ht : Tendsto primeSurvivorSlope atTop (𝓝 0)) :
    Summable primeAngularInnovation ↔ Summable factorialPrimeGain :=
  ⟨factorialPrimeGain_summable_of_angular_of_slope_zero ht,
    primeAngularInnovation_summable_of_gain⟩

theorem primeMeanMismatchBudget_tendsto_of_angular_of_slope_zero
    (ht : Tendsto primeSurvivorSlope atTop (𝓝 0))
    (hA : Summable primeAngularInnovation) :
    Tendsto primeMeanMismatchBudget atTop (𝓝 0) :=
  primeMeanMismatchBudget_tendsto_of_gain_summable
    (factorialPrimeGain_summable_of_angular_of_slope_zero ht hA)

theorem primeAngularInnovation_tsum_eq_gain_of_slope_zero
    (ht : Tendsto primeSurvivorSlope atTop (𝓝 0))
    (hA : Summable primeAngularInnovation) :
    (∑' n, primeAngularInnovation n) = ∑' n, factorialPrimeGain n := by
  have hG := factorialPrimeGain_summable_of_angular_of_slope_zero ht hA
  have hW : Tendsto primeCancellationVariance atTop
      (𝓝 (∑' n, primeAngularInnovation n)) := by
    change Tendsto (fun N => primeCancellationVariance N) atTop
      (𝓝 (∑' n, primeAngularInnovation n))
    simpa only [primeCancellationVariance_eq_sum] using hA.hasSum.tendsto_sum_nat
  have hR := primeMeanMismatchBudget_tendsto_of_angular_of_slope_zero ht hA
  have hlim : Tendsto primeGainBudget atTop
      (𝓝 (∑' n, primeAngularInnovation n)) := by
    simpa only [zero_add, ← primeGainBudget_eq_alignment] using hR.add hW
  exact tendsto_nhds_unique hlim hG.hasSum.tendsto_sum_nat

theorem tailCapacity_succ_le_two_tsum_of_slope_zero
    (ht : Tendsto primeSurvivorSlope atTop (𝓝 0))
    (hA : Summable primeAngularInnovation)
    (hJ : Summable factorialCompositeGain) (N : ℕ) :
    tailCapacity (N + 1) ≤ tailCapacity 1 +
      (∑' n, primeAngularInnovation n) + (∑' n, factorialCompositeGain n) := by
  rw [capacity_eq_prime_composite_budget]
  have ha := primeGainBudget_le_angular_tsum ht hA N
  have hj : compositeGainBudget N ≤ ∑' n, factorialCompositeGain n :=
    hJ.sum_le_tsum (Finset.range N) (fun n _ => factorialCompositeGain_nonneg n)
  linarith

theorem tailCapacity_tendsto_iff_two_gain_channels_of_slope_zero
    (ht : Tendsto primeSurvivorSlope atTop (𝓝 0)) :
    Tendsto tailCapacity atTop atTop ↔
      (¬ Summable primeAngularInnovation) ∨ (¬ Summable factorialCompositeGain) := by
  constructor
  · intro hc
    by_contra! h
    have hR := primeMeanMismatchBudget_tendsto_of_angular_of_slope_zero ht h.1
    rcases tailCapacity_tendsto_iff_prime_angular_channels.mp hc with hR' | hA | hJ
    · exact hR' hR
    · exact hA h.1
    · exact hJ h.2
  · rintro (hA | hJ)
    · exact tailCapacity_tendsto_of_primeAngularInnovation_not_summable hA
    · exact tailCapacity_tendsto_of_factorialCompositeGain_not_summable hJ

/-- The analytic rate is explicit. The exact gain decomposition precedes
the nonnegative comparison; no signed screened term is replaced. -/
theorem primeSurvivorSlope_tendsto_of_capacity_sublinear_source
    (h : Tendsto (fun N => tailCapacity (N + 1) / primeSourceBudget N)
      atTop (𝓝 0)) :
    Tendsto primeSurvivorSlope atTop (𝓝 0) := by
  have hc (N : ℕ) : primeMeanMismatchBudget N ≤ tailCapacity (N + 1) := by
    rw [capacity_eq_prime_composite_budget, primeGainBudget_eq_alignment]
    linarith [tailCapacity_nonneg 1, compositeGainBudget_nonneg N,
      primeCancellationVariance_nonneg N]
  have hs : Tendsto (fun N => (primeSurvivorSlope N) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun N => sq_nonneg _) _ h
    intro N
    by_cases hN : N = 0
    · subst N
      simp [primeSurvivorSlope, primeSourceBudget, primeCrossBudget]
    have hU := primeSourceBudget_pos N (Nat.pos_of_ne_zero hN)
    have he : (primeSurvivorSlope N) ^ 2 =
        primeMeanMismatchBudget N / primeSourceBudget N := by
      unfold primeSurvivorSlope primeMeanMismatchBudget
      field_simp [ne_of_gt hU] <;> ring
    rw [he]
    exact div_le_div_of_nonneg_right (hc N) hU.le
  have hns : Tendsto (fun N => ‖primeSurvivorSlope N‖ ^ 2) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, sq_abs] using hs
  have hn : Tendsto (fun N => ‖primeSurvivorSlope N‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hns
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using hn)

theorem tailCapacity_tendsto_iff_two_gain_channels_of_sublinear_source
    (h : Tendsto (fun N => tailCapacity (N + 1) / primeSourceBudget N)
      atTop (𝓝 0)) :
    Tendsto tailCapacity atTop atTop ↔
      (¬ Summable primeAngularInnovation) ∨ (¬ Summable factorialCompositeGain) :=
  tailCapacity_tendsto_iff_two_gain_channels_of_slope_zero
    (primeSurvivorSlope_tendsto_of_capacity_sublinear_source h)

theorem RH_iff_two_gain_channels_of_sublinear_source
    (hBaezDuarte : RiemannHypothesis →
      RiemannResearch.RH.Pareto.BaezDuarte.NaturalApproximation)
    (h : Tendsto (fun N => tailCapacity (N + 1) / primeSourceBudget N)
      atTop (𝓝 0)) :
    RiemannHypothesis ↔
      (¬ Summable primeAngularInnovation) ∨ (¬ Summable factorialCompositeGain) :=
  (RH_iff_tailCapacity_tendsto hBaezDuarte).trans
    (tailCapacity_tendsto_iff_two_gain_channels_of_sublinear_source h)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
