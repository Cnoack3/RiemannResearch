/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoPrimeSourceDivergence

/-!
# Necessary fresh-prime cancellation if RH fails

Source: continuation of the user-provided
ParetoCapacityFormalization20260921 (2).md (2026-09-21).
The exact identity eta = delta + kappa uses the actual innovation and
factorial coprime certificate at each growing dictionary.

Under not RH the actual Schur gains are summable. Consequently the signed
error energy is nonsummable, while the primes where any fixed positive
fraction of the source survives have summable reciprocal-prime mass.
All these are checked implications, not an unconditional proof of RH.
The arithmetic premises of the sufficient RH criteria remain Open.
No RH-to-density or critical-line-zero provider is used.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.Pareto.IntegerDPP
def factorialPrimeError (n : ℕ) : ℝ :=
  inner ℝ (tailInnovation (n + 1))
    (infiniteCoprimeCertificate (n + 2).factorial - tailMinimum (n + 1))

def factorialPrimeErrorEnergy (n : ℕ) : ℝ :=
  if Nat.Prime (n + 3) then (factorialPrimeError n) ^ 2 / schurSigma (n + 1) else 0

theorem factorialPrimeError_decomposition (n : ℕ) (hp : Nat.Prime (n + 3)) :
    schurEta (n + 1) = coprimePrimeDefect (n + 2).factorial (n + 3) +
      factorialPrimeError n := by
  have h := schurEta_fresh_prime_decomposition (n + 1) (n + 2).factorial
    (Nat.factorial_ne_zero _) (Nat.dvd_factorial (by omega) (by omega))
    (fun i => Nat.dvd_factorial (by omega) (by omega))
    (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hp)
    (by simpa only [hp.dvd_factorial] using (by omega : ¬ n + 3 ≤ n + 2))
  simpa only [Nat.add_assoc, Nat.reduceAdd, factorialPrimeError] using h

theorem factorialPrimeSourceEnergy_le_gain_add_error (n : ℕ) :
    factorialPrimeSourceEnergy n ≤
      2 * ((schurEta (n + 1)) ^ 2 / schurSigma (n + 1)) +
      2 * factorialPrimeErrorEnergy n := by
  by_cases hp : Nat.Prime (n + 3)
  · simp only [factorialPrimeSourceEnergy, factorialPrimeErrorEnergy, if_pos hp]
    have he := factorialPrimeError_decomposition n hp
    have hsq : (coprimePrimeDefect (n + 2).factorial (n + 3)) ^ 2 ≤
        2 * (schurEta (n + 1)) ^ 2 + 2 * (factorialPrimeError n) ^ 2 := by
      rw [he]
      nlinarith [sq_nonneg (coprimePrimeDefect (n + 2).factorial (n + 3) + 2 * factorialPrimeError n)]
    have h := div_le_div_of_nonneg_right hsq (schurSigma_pos (n + 1)).le
    calc
      _ ≤ (2 * (schurEta (n + 1)) ^ 2 + 2 * (factorialPrimeError n) ^ 2) / schurSigma (n + 1) := h
      _ = _ := by ring
  · simp only [factorialPrimeSourceEnergy, factorialPrimeErrorEnergy, if_neg hp, mul_zero, add_zero]
    exact mul_nonneg (by norm_num) (div_nonneg (sq_nonneg _) (schurSigma_pos _).le)

theorem schurGain_summable_of_not_RH (hRH : ¬ RiemannHypothesis) :
    Summable (fun n => (schurEta n) ^ 2 / schurSigma n) := by
  by_contra h
  exact hRH (riemannHypothesis_of_schur_sum_tendsto
    ((not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun n => div_nonneg (sq_nonneg _) (schurSigma_pos n).le)).mp h))

/-- CONDITIONAL RESEARCH REDUCTION: summability of the actual signed error
energy is an unresolved arithmetic premise. -/
theorem riemannHypothesis_of_factorialPrimeErrorEnergy_summable
    (hc : Summable factorialPrimeErrorEnergy) : RiemannHypothesis := by
  by_contra hRH
  have hg := (summable_nat_add_iff 1).mpr (schurGain_summable_of_not_RH hRH)
  exact factorialPrimeSourceEnergy_not_summable
    (Summable.of_nonneg_of_le factorialPrimeSourceEnergy_nonneg
      factorialPrimeSourceEnergy_le_gain_add_error ((hg.mul_left 2).add (hc.mul_left 2)))

theorem factorialPrimeErrorEnergy_not_summable_of_not_RH (hRH : ¬ RiemannHypothesis) :
    ¬ Summable factorialPrimeErrorEnergy :=
  fun hc => hRH (riemannHypothesis_of_factorialPrimeErrorEnergy_summable hc)

/-- Reciprocal-prime mass of stages where at least an epsilon fraction
of the positive source survives its actual signed correction. -/
def primeNoncancellationMass (ε : ℝ) (n : ℕ) : ℝ :=
  if Nat.Prime (n + 3) ∧
      ε * coprimePrimeDefect (n + 2).factorial (n + 3) ≤
        |coprimePrimeDefect (n + 2).factorial (n + 3) + factorialPrimeError n|
  then 1 / ((n + 3 : ℕ) : ℝ) else 0

theorem primeNoncancellationMass_nonneg (ε : ℝ) (n : ℕ) :
    0 ≤ primeNoncancellationMass ε n := by
  unfold primeNoncancellationMass
  split_ifs <;> positivity

theorem primeNoncancellationMass_le_schurGain (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    primeNoncancellationMass ε n ≤
      (8 / ε ^ 2) * ((schurEta (n + 1)) ^ 2 / schurSigma (n + 1)) := by
  unfold primeNoncancellationMass
  split_ifs with h
  · have hδ : 0 ≤ coprimePrimeDefect (n + 2).factorial (n + 3) :=
      (coprimePrimeDefect_pos _ _ (Nat.factorial_ne_zero _)
        (Nat.dvd_factorial (by omega) (by omega)) (by omega)).le
    have hsquare := pow_le_pow_left₀ (mul_nonneg hε.le hδ) h.2 2
    rw [sq_abs, ← factorialPrimeError_decomposition n h.1, mul_pow] at hsquare
    have hgain := div_le_div_of_nonneg_right hsquare (schurSigma_pos (n + 1)).le
    have hl := factorialPrimeDefect_normalized_lower (n + 1) (by omega)
    simp only [Nat.add_assoc, Nat.reduceAdd] at hl
    have hlε := mul_le_mul_of_nonneg_left hl (sq_nonneg ε)
    have he : ε ^ 2 * (1 / (8 * ((n + 3 : ℕ) : ℝ))) =
        (ε ^ 2 / 8) * (1 / ((n + 3 : ℕ) : ℝ)) := by ring
    rw [he] at hlε
    have hmain : (ε ^ 2 / 8) * (1 / ((n + 3 : ℕ) : ℝ)) ≤
        (schurEta (n + 1)) ^ 2 / schurSigma (n + 1) := by
      have he' : ε ^ 2 *
          ((coprimePrimeDefect (n + 2).factorial (n + 3)) ^ 2 / schurSigma (n + 1)) =
          (ε ^ 2 * (coprimePrimeDefect (n + 2).factorial (n + 3)) ^ 2) /
            schurSigma (n + 1) := by ring
      rw [he'] at hlε
      exact hlε.trans hgain
    have hscaled := mul_le_mul_of_nonneg_left hmain
      (by positivity : 0 ≤ 8 / ε ^ 2)
    have hcancel : (8 / ε ^ 2) * ((ε ^ 2 / 8) *
        (1 / ((n + 3 : ℕ) : ℝ))) = 1 / ((n + 3 : ℕ) : ℝ) := by
      field_simp
    simpa only [hcancel] using hscaled
  · exact mul_nonneg (by positivity)
      (div_nonneg (sq_nonneg _) (schurSigma_pos _).le)

/-- Under not RH, every fixed tolerance leaves only a summable
reciprocal-prime exceptional set. No density provider is used. -/
theorem primeNoncancellationMass_summable_of_not_RH
    (hRH : ¬ RiemannHypothesis) (ε : ℝ) (hε : 0 < ε) :
    Summable (primeNoncancellationMass ε) := by
  have hg := (summable_nat_add_iff 1).mpr (schurGain_summable_of_not_RH hRH)
  exact Summable.of_nonneg_of_le (primeNoncancellationMass_nonneg ε)
    (primeNoncancellationMass_le_schurGain ε hε) (hg.mul_left (8 / ε ^ 2))

/-- CONDITIONAL RESEARCH REDUCTION: the positive-reciprocal-mass
noncancellation premise remains an open arithmetic obligation. -/
theorem riemannHypothesis_of_primeNoncancellationMass_not_summable
    (ε : ℝ) (hε : 0 < ε) (h : ¬ Summable (primeNoncancellationMass ε)) :
    RiemannHypothesis := by
  by_contra hRH
  exact h (primeNoncancellationMass_summable_of_not_RH hRH ε hε)

/-- CONDITIONAL RESEARCH REDUCTION: the uniform relative noncancellation
premise is not established here. -/
theorem riemannHypothesis_of_uniform_prime_noncancellation
    (ε : ℝ) (hε : 0 < ε)
    (h : ∀ n : ℕ, Nat.Prime (n + 3) →
      ε * coprimePrimeDefect (n + 2).factorial (n + 3) ≤
        |coprimePrimeDefect (n + 2).factorial (n + 3) + factorialPrimeError n|) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_primeNoncancellationMass_not_summable ε hε
  intro hs
  apply not_summable_one_div_on_primes
  apply (summable_nat_add_iff 3).mp
  have he (n : ℕ) : primeNoncancellationMass ε n =
      ({p : ℕ | Nat.Prime p}.indicator (fun p => 1 / (p : ℝ))) (n + 3) := by
    by_cases hp : Nat.Prime (n + 3)
    · simp [primeNoncancellationMass, hp, h n hp]
    · simp [primeNoncancellationMass, hp]
  exact hs.congr he


end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
