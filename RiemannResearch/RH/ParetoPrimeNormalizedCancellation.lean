/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoPrimeCancellation

/-!
# Prime-harmonic normalized cancellation

Source: continuation of the user-provided
`ParetoCapacityFormalization20260921_Continued(1).md` (2026-09-21).

At every fresh-prime stage the actual signed Schur numerator is
`eta = delta + kappa`. This module divides by the positive arithmetic
source `delta` and proves that not RH forces the relative survivor
`1 + kappa / delta` to be square summable with reciprocal-prime weight.

This is an unconditional necessary condition for not RH and a conditional
research reduction in the reverse direction. It does not establish the
open arithmetic nonsummability premise and does not prove RH.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.Pareto.IntegerDPP

def factorialPrimeDelta (n : ℕ) : ℝ :=
  coprimePrimeDefect (n + 2).factorial (n + 3)

def factorialPrimeRelativeCancellationEnergy (n : ℕ) : ℝ :=
  if Nat.Prime (n + 3) then
    (1 / ((n + 3 : ℕ) : ℝ)) *
      (1 + factorialPrimeError n / factorialPrimeDelta n) ^ 2
  else 0

theorem factorialPrimeDelta_pos (n : ℕ) :
    0 < factorialPrimeDelta n := by
  apply coprimePrimeDefect_pos (n + 2).factorial (n + 3)
  · exact Nat.factorial_ne_zero _
  · exact Nat.dvd_factorial (by decide) (by omega)
  · omega

theorem factorialPrimeRelativeCancellationEnergy_nonneg (n : ℕ) :
    0 ≤ factorialPrimeRelativeCancellationEnergy n := by
  unfold factorialPrimeRelativeCancellationEnergy
  split_ifs <;> positivity

theorem factorialPrimeRelativeCancellationEnergy_eq
    (n : ℕ) (hp : Nat.Prime (n + 3)) :
    factorialPrimeRelativeCancellationEnergy n =
      (schurEta (n + 1)) ^ 2 /
        (((n + 3 : ℕ) : ℝ) * (factorialPrimeDelta n) ^ 2) := by
  simp only [factorialPrimeRelativeCancellationEnergy, if_pos hp]
  have he : schurEta (n + 1) =
      factorialPrimeDelta n + factorialPrimeError n := by
    simpa only [factorialPrimeDelta] using factorialPrimeError_decomposition n hp
  rw [he]
  field_simp [ne_of_gt (factorialPrimeDelta_pos n)]

theorem factorialPrimeRelativeCancellationEnergy_le_gain (n : ℕ) :
    factorialPrimeRelativeCancellationEnergy n ≤
      8 * ((schurEta (n + 1)) ^ 2 / schurSigma (n + 1)) := by
  by_cases hp : Nat.Prime (n + 3)
  · rw [factorialPrimeRelativeCancellationEnergy_eq n hp]
    have hl := factorialPrimeDefect_normalized_lower (n + 1) (by omega)
    simp only [Nat.add_assoc, Nat.reduceAdd] at hl
    change 1 / (8 * ((n + 3 : ℕ) : ℝ)) ≤
      (factorialPrimeDelta n) ^ 2 / schurSigma (n + 1) at hl
    have hq : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := by positivity
    have hδ : 0 < factorialPrimeDelta n := factorialPrimeDelta_pos n
    have hσ : 0 < schurSigma (n + 1) := schurSigma_pos (n + 1)
    have hσupper :
        schurSigma (n + 1) ≤
          (factorialPrimeDelta n) ^ 2 * (8 * ((n + 3 : ℕ) : ℝ)) := by
      have h := (div_le_div_iff₀ (by positivity : (0 : ℝ) <
          8 * ((n + 3 : ℕ) : ℝ)) hσ).mp hl
      simpa only [one_mul] using h
    have hcross :
        (schurEta (n + 1)) ^ 2 * schurSigma (n + 1) ≤
          (8 * (schurEta (n + 1)) ^ 2) *
            (((n + 3 : ℕ) : ℝ) * (factorialPrimeDelta n) ^ 2) := by
      have hm := mul_nonneg (sq_nonneg (schurEta (n + 1)))
        (sub_nonneg.mpr hσupper)
      nlinarith
    calc
      (schurEta (n + 1)) ^ 2 /
          (((n + 3 : ℕ) : ℝ) * (factorialPrimeDelta n) ^ 2) ≤
          (8 * (schurEta (n + 1)) ^ 2) / schurSigma (n + 1) := by
            exact (div_le_div_iff₀
              (mul_pos hq (sq_pos_of_pos hδ)) hσ).2 hcross
      _ = 8 * ((schurEta (n + 1)) ^ 2 / schurSigma (n + 1)) := by ring
  · simp only [factorialPrimeRelativeCancellationEnergy, if_neg hp]
    exact mul_nonneg (by norm_num)
      (div_nonneg (sq_nonneg _) (schurSigma_pos _).le)

theorem factorialPrimeRelativeCancellationEnergy_summable_of_not_RH
    (hRH : ¬ RiemannHypothesis) :
    Summable factorialPrimeRelativeCancellationEnergy := by
  have hg := (summable_nat_add_iff 1).mpr (schurGain_summable_of_not_RH hRH)
  exact Summable.of_nonneg_of_le
    factorialPrimeRelativeCancellationEnergy_nonneg
    factorialPrimeRelativeCancellationEnergy_le_gain
    (hg.mul_left 8)

/-- CONDITIONAL RESEARCH REDUCTION: nonsummability of the normalized
relative survivor is an open arithmetic premise. -/
theorem riemannHypothesis_of_relativeCancellationEnergy_not_summable
    (h : ¬ Summable factorialPrimeRelativeCancellationEnergy) :
    RiemannHypothesis := by
  by_contra hRH
  exact h (factorialPrimeRelativeCancellationEnergy_summable_of_not_RH hRH)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
