/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoFirstSiteRHConsequences

/-!
# Exact accumulation of prime cancellation variance

Source: finite weighted regression square completion. The complete screened
factorial/CRT correction is retained in each determinant. This derives a
monotone angular channel and an exact three-channel first-site provider.
No divergence of an arithmetic channel or unconditional RH is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.WeightedScalarEnergy
open RiemannResearch.RH.Pareto.IntegerDPP

/-- Exact new centered variance when the prospective prime row is added.
At the empty initial budget this is zero by real division by zero. -/
def primeAngularInnovation (N : ℕ) : ℝ :=
  primeSchurWeight N *
    (primeSourceBudget N * factorialPrimeError N -
      primeCrossBudget N * factorialPrimeDelta N) ^ 2 /
    (primeSourceBudget N *
      (primeSourceBudget N + primeSchurWeight N * (factorialPrimeDelta N) ^ 2))

theorem primeSourceBudget_succ_weighted (N : ℕ) :
    primeSourceBudget (N + 1) = primeSourceBudget N +
      primeSchurWeight N * (factorialPrimeDelta N) ^ 2 := by
  simp only [primeSourceBudget_eq_weighted, square, Finset.sum_range_succ]

theorem primeErrorBudget_succ_weighted (N : ℕ) :
    primeErrorBudget (N + 1) = primeErrorBudget N +
      primeSchurWeight N * (factorialPrimeError N) ^ 2 := by
  simp only [primeErrorBudget_eq_weighted, square, Finset.sum_range_succ]

theorem primeCrossBudget_succ_weighted (N : ℕ) :
    primeCrossBudget (N + 1) = primeCrossBudget N +
      primeSchurWeight N * factorialPrimeDelta N * factorialPrimeError N := by
  simp only [primeCrossBudget_eq_weighted, product, Finset.sum_range_succ]

theorem primeCancellationVariance_eq_quotient (N : ℕ) (hN : 0 < N) :
    primeCancellationVariance N =
      primeErrorBudget N - (primeCrossBudget N) ^ 2 / primeSourceBudget N := by
  rw [primeCancellationVariance_eq_pair_budget N hN, primePairCancellationBudget_eq]
  field_simp [ne_of_gt (primeSourceBudget_pos N hN)]

theorem primeAngularInnovation_nonneg (N : ℕ) :
    0 ≤ primeAngularInnovation N := by
  unfold primeAngularInnovation
  exact div_nonneg
    (mul_nonneg (primeSchurWeight_nonneg N) (sq_nonneg _))
    (mul_nonneg (primeSourceBudget_nonneg N)
      (add_nonneg (primeSourceBudget_nonneg N)
        (mul_nonneg (primeSchurWeight_nonneg N) (sq_nonneg _))))

@[simp] theorem primeAngularInnovation_zero : primeAngularInnovation 0 = 0 := by
  simp [primeAngularInnovation, primeSourceBudget, primeCrossBudget]

@[simp] theorem primeCancellationVariance_zero : primeCancellationVariance 0 = 0 := by
  simp [primeCancellationVariance, square]

@[simp] theorem primeCancellationVariance_one : primeCancellationVariance 1 = 0 := by
  rw [primeCancellationVariance_eq_pair_budget 1 (by omega)]
  simp [primePairCancellationBudget]

/-- The complete determinant square is retained before nonnegativity is used. -/
theorem primeCancellationVariance_succ (N : ℕ) :
    primeCancellationVariance (N + 1) =
      primeCancellationVariance N + primeAngularInnovation N := by
  by_cases hN : N = 0
  · subst N
    simp
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hU : primeSourceBudget N ≠ 0 := ne_of_gt (primeSourceBudget_pos N hNpos)
  have hU' : primeSourceBudget N +
      primeSchurWeight N * (factorialPrimeDelta N) ^ 2 ≠ 0 := by
    rw [← primeSourceBudget_succ_weighted]
    exact ne_of_gt (primeSourceBudget_pos (N + 1) (by omega))
  rw [primeCancellationVariance_eq_quotient (N + 1) (by omega),
    primeCancellationVariance_eq_quotient N hNpos,
    primeSourceBudget_succ_weighted, primeErrorBudget_succ_weighted,
    primeCrossBudget_succ_weighted]
  exact centered_energy_update _ _ _ _ _ _ hU hU'

theorem primeCancellationVariance_monotone : Monotone primeCancellationVariance := by
  apply monotone_nat_of_le_succ
  intro N
  rw [primeCancellationVariance_succ]
  exact le_add_of_nonneg_right (primeAngularInnovation_nonneg N)

theorem primeCancellationVariance_eq_sum (N : ℕ) :
    primeCancellationVariance N =
      ∑ n ∈ Finset.range N, primeAngularInnovation n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [primeCancellationVariance_succ, Finset.sum_range_succ, ih]

/-- Exact capacity accounting with the monotone angular channel exposed. -/
theorem capacity_eq_prime_angular_budget (N : ℕ) (hN : 0 < N) :
    tailCapacity (N + 1) = tailCapacity 1 + primeMeanMismatchBudget N +
      (∑ n ∈ Finset.range N, primeAngularInnovation n) + compositeGainBudget N := by
  rw [capacity_eq_prime_alignment_budget N hN, primeCancellationVariance_eq_sum]

theorem primeGainBudget_eq_alignment (N : ℕ) :
    primeGainBudget N = primeMeanMismatchBudget N + primeCancellationVariance N := by
  by_cases hN : N = 0
  · subst N
    simp [primeGainBudget, primeMeanMismatchBudget, primeSourceBudget, primeCrossBudget]
  have h1 := capacity_eq_prime_composite_budget N
  have h2 := capacity_eq_prime_alignment_budget N (Nat.pos_of_ne_zero hN)
  linarith

/-- The mean channel can decrease; the angular increment then retains the gain. -/
theorem primeMeanMismatchBudget_step (N : ℕ) :
    primeMeanMismatchBudget (N + 1) + primeAngularInnovation N =
      primeMeanMismatchBudget N + factorialPrimeGain N := by
  have hg : primeGainBudget (N + 1) = primeGainBudget N + factorialPrimeGain N := by
    simp only [primeGainBudget, Finset.sum_range_succ]
  rw [primeGainBudget_eq_alignment, primeGainBudget_eq_alignment,
    primeCancellationVariance_succ] at hg
  linarith

theorem tailCapacity_tendsto_iff_prime_angular_unbounded :
    Tendsto tailCapacity atTop atTop ↔
      ∀ B : ℝ, ∃ N : ℕ, 0 < N ∧
        B < primeMeanMismatchBudget N +
          (∑ n ∈ Finset.range N, primeAngularInnovation n) + compositeGainBudget N := by
  simpa only [primeCancellationVariance_eq_sum] using
    tailCapacity_tendsto_iff_prime_alignment_unbounded

/-- CONDITIONAL RESEARCH REDUCTION: the actual angular series remains Open. -/
theorem tailCapacity_tendsto_of_primeAngularInnovation_not_summable
    (h : ¬ Summable primeAngularInnovation) :
    Tendsto tailCapacity atTop atTop := by
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    primeAngularInnovation_nonneg).mp h
  apply tailCapacity_tendsto_iff_prime_angular_unbounded.mpr
  intro B
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht) (B + 1))
  have hh := hN (N + 1) (Nat.le_succ N)
  exact ⟨N + 1, by omega, by
    linarith [primeMeanMismatchBudget_nonneg (N + 1), compositeGainBudget_nonneg (N + 1)]⟩

theorem riemannHypothesis_of_primeAngularInnovation_not_summable
    (h : ¬ Summable primeAngularInnovation) : RiemannHypothesis :=
  riemannHypothesis_of_tailCapacity_tendsto
    (tailCapacity_tendsto_of_primeAngularInnovation_not_summable h)

theorem primeAngularInnovation_summable_of_not_RH
    (hRH : ¬ RiemannHypothesis) : Summable primeAngularInnovation := by
  by_contra h
  exact hRH (riemannHypothesis_of_primeAngularInnovation_not_summable h)

/-- Full signed relative error compared with its accumulated regression slope. -/
def primeRelativeAngularEnergy (N : ℕ) : ℝ :=
  if 0 < N ∧ Nat.Prime (N + 3) then
    (factorialPrimeError N / factorialPrimeDelta N -
      primeCrossBudget N / primeSourceBudget N) ^ 2 / ((N + 3 : ℕ) : ℝ)
  else 0

theorem primeRelativeAngularEnergy_nonneg (N : ℕ) :
    0 ≤ primeRelativeAngularEnergy N := by
  unfold primeRelativeAngularEnergy
  split_ifs
  · exact div_nonneg (sq_nonneg _) (by positivity)
  · exact le_rfl

theorem primeAngularInnovation_eq_relative (N : ℕ) (hN : 0 < N) :
    primeAngularInnovation N =
      (primeSchurWeight N * (factorialPrimeDelta N) ^ 2 * primeSourceBudget N /
        (primeSourceBudget N + primeSchurWeight N * (factorialPrimeDelta N) ^ 2)) *
      (factorialPrimeError N / factorialPrimeDelta N -
        primeCrossBudget N / primeSourceBudget N) ^ 2 := by
  have hU := ne_of_gt (primeSourceBudget_pos N hN)
  have hd := ne_of_gt (factorialPrimeDelta_pos N)
  have hU' : primeSourceBudget N +
      primeSchurWeight N * (factorialPrimeDelta N) ^ 2 ≠ 0 := by
    rw [← primeSourceBudget_succ_weighted]
    exact ne_of_gt (primeSourceBudget_pos (N + 1) (by omega))
  unfold primeAngularInnovation
  field_simp [hU, hd, hU']

theorem primeSourceBudget_ge_one_div_twentyfour (N : ℕ) (hN : 0 < N) :
    (1 : ℝ) / 24 ≤ primeSourceBudget N := by
  have h1 : (1 : ℝ) / 24 ≤ primeSourceBudget 1 := by
    have hl := factorialPrimeDefect_normalized_lower 1 (by omega)
    norm_num at hl
    simpa [primeSourceBudget, factorialPrimeSourceEnergy, (by decide : Nat.Prime 3)] using hl
  exact h1.trans (primeSourceBudget_monotone (by omega : 1 ≤ N))

/-- Unconditional arithmetic lower weight. The actual Schur pivot is retained. -/
theorem primeRelativeAngularEnergy_le (N : ℕ) :
    primeRelativeAngularEnergy N ≤ 16 * primeAngularInnovation N := by
  by_cases h : 0 < N ∧ Nat.Prime (N + 3)
  · rw [primeRelativeAngularEnergy, if_pos h, primeAngularInnovation_eq_relative N h.1]
    let u := primeSchurWeight N * (factorialPrimeDelta N) ^ 2
    let U := primeSourceBudget N
    let p : ℝ := ((N + 3 : ℕ) : ℝ)
    let t := factorialPrimeError N / factorialPrimeDelta N -
      primeCrossBudget N / primeSourceBudget N
    have hU : 0 < U := primeSourceBudget_pos N h.1
    have hu : 0 ≤ u := mul_nonneg (primeSchurWeight_nonneg N) (sq_nonneg _)
    have hp : 0 < p := by dsimp [p]; positivity
    have huv : 1 / (8 * p) ≤ u := by
      simpa [u, p, primeSchurWeight, h.2, factorialPrimeDelta, div_eq_mul_inv,
        mul_comm, Nat.add_assoc] using
        factorialPrimeDefect_normalized_lower (N + 1) (by omega)
    have hUv : 1 / (8 * p) ≤ U := by
      have hp3 : 3 ≤ p := by dsimp [p]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) N]
      have hb : 1 / (8 * p) ≤ (1 : ℝ) / 24 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      exact hb.trans (primeSourceBudget_ge_one_div_twentyfour N h.1)
    have hr : 1 / (16 * p) ≤ u * U / (U + u) := by
      have hh := reduced_weight_lower u U (1 / (8 * p)) hU hu hUv huv
      convert hh using 1
      ring
    have ht := mul_le_mul_of_nonneg_right hr (sq_nonneg t)
    change t ^ 2 / p ≤ 16 * (u * U / (U + u) * t ^ 2)
    have he : t ^ 2 / p = 16 * (1 / (16 * p) * t ^ 2) := by ring
    rw [he]
    linarith
  · rw [primeRelativeAngularEnergy, if_neg h]
    exact mul_nonneg (by norm_num) (primeAngularInnovation_nonneg N)

theorem primeRelativeAngularEnergy_summable_of_angular
    (h : Summable primeAngularInnovation) : Summable primeRelativeAngularEnergy :=
  Summable.of_nonneg_of_le primeRelativeAngularEnergy_nonneg
    primeRelativeAngularEnergy_le (h.mul_left 16)

theorem primeRelativeAngularEnergy_summable_of_not_RH
    (hRH : ¬ RiemannHypothesis) : Summable primeRelativeAngularEnergy :=
  primeRelativeAngularEnergy_summable_of_angular
    (primeAngularInnovation_summable_of_not_RH hRH)

/-- CONDITIONAL RESEARCH REDUCTION: nonsummable reciprocal-prime centered
relative cancellation is a sufficient actual arithmetic provider, still Open. -/
theorem tailCapacity_tendsto_of_primeRelativeAngularEnergy_not_summable
    (h : ¬ Summable primeRelativeAngularEnergy) :
    Tendsto tailCapacity atTop atTop := by
  apply tailCapacity_tendsto_of_primeAngularInnovation_not_summable
  intro ha
  exact h (primeRelativeAngularEnergy_summable_of_angular ha)

theorem riemannHypothesis_of_primeRelativeAngularEnergy_not_summable
    (h : ¬ Summable primeRelativeAngularEnergy) : RiemannHypothesis :=
  riemannHypothesis_of_tailCapacity_tendsto
    (tailCapacity_tendsto_of_primeRelativeAngularEnergy_not_summable h)

theorem tailCapacity_tendsto_of_factorialCompositeGain_not_summable
    (h : ¬ Summable factorialCompositeGain) :
    Tendsto tailCapacity atTop atTop := by
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    factorialCompositeGain_nonneg).mp h
  apply tailCapacity_tendsto_iff_prime_alignment_unbounded.mpr
  intro B
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht) (B + 1))
  have hh := hN (N + 1) (Nat.le_succ N)
  change B + 1 ≤ compositeGainBudget (N + 1) at hh
  exact ⟨N + 1, by omega, by
    linarith [primeMeanMismatchBudget_nonneg (N + 1),
      primeCancellationVariance_nonneg (N + 1)]⟩

/-- All three failure conditions yield a finite capacity bound; no growing
prime row or nonprime gain is omitted. -/
theorem tailCapacity_bounded_of_prime_angular_failure
    (hR : Tendsto primeMeanMismatchBudget atTop (𝓝 0))
    (hA : Summable primeAngularInnovation)
    (hJ : Summable factorialCompositeGain) :
    ∃ B : ℝ, ∀ n : ℕ, tailCapacity n ≤ B := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_order.mp hR).2 1 (by norm_num))
  let B := tailCapacity 1 + 1 +
    (∑' n, primeAngularInnovation n) + (∑' n, factorialCompositeGain n)
  refine ⟨B, fun n => ?_⟩
  let M := max n (N₀ + 1)
  have hM : N₀ ≤ M := by dsimp [M]; omega
  have hMp : 0 < M := by dsimp [M]; omega
  have hR' : primeMeanMismatchBudget M < 1 := hN₀ M hM
  have hA' : (∑ k ∈ Finset.range M, primeAngularInnovation k) ≤
      ∑' k, primeAngularInnovation k :=
    hA.sum_le_tsum (Finset.range M) (fun k _ => primeAngularInnovation_nonneg k)
  have hJ' : compositeGainBudget M ≤ ∑' k, factorialCompositeGain k :=
    hJ.sum_le_tsum (Finset.range M) (fun k _ => factorialCompositeGain_nonneg k)
  have hCM : tailCapacity (M + 1) ≤ B := by
    rw [capacity_eq_prime_angular_budget M hMp]
    dsimp [B]
    linarith
  exact (tailCapacity_monotone (show n ≤ M + 1 by dsimp [M]; omega)).trans hCM

/-- Exact failure alternative. No individual arithmetic channel is asserted
necessary on its own, and none is supplied unconditionally. -/
theorem tailCapacity_tendsto_iff_prime_angular_channels :
    Tendsto tailCapacity atTop atTop ↔
      (¬ Tendsto primeMeanMismatchBudget atTop (𝓝 0)) ∨
      (¬ Summable primeAngularInnovation) ∨ (¬ Summable factorialCompositeGain) := by
  constructor
  · intro ht
    by_contra! h
    obtain ⟨B, hB⟩ := tailCapacity_bounded_of_prime_angular_failure h.1 h.2.1 h.2.2
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht) (B + 1))
    linarith [hN N le_rfl, hB N]
  · intro h
    rcases h with hR | hA | hJ
    · exact tailCapacity_tendsto_of_prime_mean_mismatch_not_tendsto hR
    · exact tailCapacity_tendsto_of_primeAngularInnovation_not_summable hA
    · exact tailCapacity_tendsto_of_factorialCompositeGain_not_summable hJ

/-- The analytic RH-to-approximation provider remains explicit. -/
theorem RH_iff_prime_angular_channels
    (hBaezDuarte : RiemannHypothesis →
      RiemannResearch.RH.Pareto.BaezDuarte.NaturalApproximation) :
    RiemannHypothesis ↔
      (¬ Tendsto primeMeanMismatchBudget atTop (𝓝 0)) ∨
      (¬ Summable primeAngularInnovation) ∨ (¬ Summable factorialCompositeGain) :=
  (RH_iff_tailCapacity_tendsto hBaezDuarte).trans
    tailCapacity_tendsto_iff_prime_angular_channels

/-- Exact screened CRT expression inside the relative angular square. -/
theorem primeRelativeAngularEnergy_eq_screened_rows (N : ℕ) :
    primeRelativeAngularEnergy N =
      if 0 < N ∧ Nat.Prime (N + 3) then
        ((inner ℝ (tailInnovation (N + 1))
            (infiniteCoprimeCertificate (Nat.factorial 2)) +
          ∑ j ∈ Finset.range N, factorialPrimeCrossGram N j) /
          factorialPrimeDelta N - primeCrossBudget N / primeSourceBudget N) ^ 2 /
            ((N + 3 : ℕ) : ℝ)
      else 0 := by
  unfold primeRelativeAngularEnergy
  rw [factorialPrimeError_eq_base_add_crossGram]

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
