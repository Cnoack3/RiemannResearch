/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoCoprimeCompositeObservation
import RiemannResearch.RH.ParetoFactorialRefinementArithmetic

/-!
# Exact full-dictionary screening of the odd reciprocal-square source

Source: continuation of the user-provided Pareto capacity handoff (2026-09-21).
The raw arithmetic matrix is evaluated on all moduli. Its complete source
is supported on odd moduli and has exact sum pi^2/8. The actual screened
row is its full inverse-Gram residual; composite dictionary rows remain.
Nonsummability of the normalized screened energy remains Open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

open RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteHilbertGram

theorem tailAtom_inner_factorialPrimeRefinement_all (k m : ℕ) :
    inner ℝ (tailAtom k) (factorialPrimeRefinement m) =
      coprimeObservationDefect (m+2).factorial (k+2) -
      coprimeObservationDefect (m+3).factorial (k+2) := by
  rw [factorialPrimeRefinement, inner_sub_right,
    infiniteCoprimeCertificate_all_observations _ _ (Nat.factorial_ne_zero _)
      (Nat.dvd_factorial (by decide) (by omega)),
    infiniteCoprimeCertificate_all_observations _ _ (Nat.factorial_ne_zero _)
      (Nat.dvd_factorial (by decide) (by omega))]
  ring

/-- The finite raw column sum on every old or new dictionary row. -/
theorem tailAtom_factorialRefinement_sum_all (n k : ℕ) (hk : k < n+2) :
    inner ℝ (tailAtom k) (∑ m ∈ Finset.range (n+1), factorialPrimeRefinement m) =
      coprimeObservationDefect 2 (k+2) := by
  have ht := factorialCoprimeCertificate_eq_base_add_refinements (n+1)
  have he := congrArg (fun x => inner ℝ (tailAtom k) x) ht
  simp only [inner_add_right, Nat.add_assoc, Nat.reduceAdd] at he
  have hz := infiniteCoprimeCertificate_observation (n+2) (n+3).factorial
    (Nat.factorial_ne_zero _) (Nat.dvd_factorial (by decide) (by omega))
    (fun i => Nat.dvd_factorial (by omega) (by omega)) ⟨k,hk⟩
  simp only [reciprocalSource] at hz
  rw [hz, infiniteCoprimeCertificate_all_observations _ _ (by decide) (by decide)] at he
  norm_num only [Nat.factorial] at he
  linarith

/-- The raw source is supported on odd moduli, including odd composites. -/
theorem coprimeObservationDefect_two (k : ℕ) :
    coprimeObservationDefect 2 (k+2) =
      if 2 ∣ k+2 then 0 else
        (1 + ‖infiniteCoprimeCertificate 2‖^2 / 2) / ((k+2 : ℕ) : ℝ)^2 := by
  have hc : Nat.Coprime (k+2) 2 ↔ ¬ 2 ∣ k+2 := by
    rw [Nat.coprime_comm]
    exact Nat.prime_two.coprime_iff_not_dvd
  unfold coprimeObservationDefect
  simp only [hc]
  by_cases hd : 2 ∣ k+2
  · simp [hd]
  · simp only [hd, not_false_eq_true, if_true, if_false]
    exact coprimePrimeDefect_energy_identity 2 (k+2) (by decide) (by decide)

theorem tailInnovation_pairing_inverseGram (k : ℕ) (x : ThresholdHilbert) :
    inner ℝ (tailInnovation k) x = inner ℝ (tailAtom k) x -
      ∑ i : Fin k, inverseCoeff (finiteTailAtom_independent k) (tailAtom k) i *
        inner ℝ (tailAtom i.val) x := by
  rw [tailInnovation, screened, inner_sub_left, inner_synthesis_left]

/-- Exact screening of the explicit raw defect. All old dictionary rows,
including composite moduli, occur in the inverse Gram coefficients. -/
theorem factorialCrossGramRow_eq_screened_defect (n : ℕ) :
    factorialCrossGramRow n = coprimeObservationDefect 2 (n+3) -
      ∑ i : Fin (n+1),
        inverseCoeff (finiteTailAtom_independent (n+1)) (tailAtom (n+1)) i *
          coprimeObservationDefect 2 (i.val+2) := by
  change (∑ m ∈ Finset.range (n+1),
    inner ℝ (tailInnovation (n+1)) (factorialPrimeRefinement m)) = _
  rw [← inner_sum, tailInnovation_pairing_inverseGram,
    tailAtom_factorialRefinement_sum_all n (n+1) (by omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [tailAtom_factorialRefinement_sum_all n i.val (by omega)]

theorem factorialCrossGramRowEnergy_eq_screened_defect (n : ℕ) :
    factorialCrossGramRowEnergy n =
      (coprimeObservationDefect 2 (n+3) -
        ∑ i : Fin (n+1),
          inverseCoeff (finiteTailAtom_independent (n+1)) (tailAtom (n+1)) i *
            coprimeObservationDefect 2 (i.val+2))^2 / schurSigma (n+1) := by
  rw [factorialCrossGramRowEnergy, factorialCrossGramRow_eq_screened_defect]


/-- The complete raw source has a finite, exactly evaluated absolute sum. -/
theorem coprimeObservationDefect_two_hasSum :
    HasSum (fun k => coprimeObservationDefect 2 (k+2))
      (coprimeReciprocalSquareMass 2) := by
  let S := coprimeReciprocalSquareMass 2 - 1
  have hS : S ≠ 0 := by
    simpa only [S, coprimeReciprocalSquareMass, add_sub_cancel_left] using
      ne_of_gt (coprimePairMass_tsum_pos 2 (by decide) (by decide))
  have hs : HasSum (fun j => coprimePairMass 2 (j+2)) S := by
    apply (hasSum_nat_add_iff 2).mpr
    have hz : (∑ j ∈ Finset.range 2, coprimePairMass 2 j) = 0 := by
      norm_num [Finset.sum_range_succ, coprimePairMass, coprimePairIndex]
    rw [hz, add_zero]
    simpa only [S, coprimeReciprocalSquareMass, add_sub_cancel_left] using
      (coprimePairMass_summable 2).hasSum
  have he (k : ℕ) : coprimeObservationDefect 2 (k+2) =
      (coprimeReciprocalSquareMass 2 / S) * coprimePairMass 2 (k+2) := by
    have hd := coprime_reciprocalSquare_decomposition_of_even 2 (k+2) (by decide)
    have hn : k+2 ≠ 1 := by omega
    simp only [hn, if_false, zero_add] at hd
    rw [← hd]
    unfold coprimeObservationDefect coprimePrimeDefect
    split_ifs <;> dsimp [S] <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring
  have hout := hs.mul_left (coprimeReciprocalSquareMass 2 / S)
  have hv : coprimeReciprocalSquareMass 2 / S * S =
      coprimeReciprocalSquareMass 2 := by field_simp
  rw [hv] at hout
  have hfun : (fun k => coprimeObservationDefect 2 (k+2)) =
      (fun k => (coprimeReciprocalSquareMass 2 / S) * coprimePairMass 2 (k+2)) := funext he
  rw [hfun]
  exact hout

theorem coprimeReciprocalSquareMass_two :
    coprimeReciprocalSquareMass 2 = Real.pi^2 / 8 := by
  rw [coprimeReciprocalSquareMass_eulerProduct 2 (by decide) (by decide),
    Nat.prime_two.primeFactors]
  norm_num
  ring

theorem coprimeObservationDefect_two_explicit (k : ℕ) :
    coprimeObservationDefect 2 (k+2) =
      if 2 ∣ k+2 then 0 else
        Real.pi^2 / ((Real.pi^2 - 8) * ((k+2 : ℕ) : ℝ)^2) := by
  have hc : Nat.Coprime (k+2) 2 ↔ ¬ 2 ∣ k+2 := by
    rw [Nat.coprime_comm]
    exact Nat.prime_two.coprime_iff_not_dvd
  unfold coprimeObservationDefect coprimePrimeDefect
  simp only [hc]
  rw [coprimeReciprocalSquareMass_two]
  by_cases hd : 2 ∣ k+2
  · simp [hd]
  · simp only [hd, not_false_eq_true, if_true, if_false]
    have he : Real.pi^2 / 8 - 1 = (Real.pi^2 - 8) / 8 := by ring
    rw [he]
    field_simp

/-- The explicit nonnegative raw source is summable, with exact sum pi^2/8. -/
theorem coprimeObservationDefect_two_hasSum_pi :
    HasSum (fun k => coprimeObservationDefect 2 (k+2)) (Real.pi^2 / 8) := by
  rw [← coprimeReciprocalSquareMass_two]
  exact coprimeObservationDefect_two_hasSum

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
