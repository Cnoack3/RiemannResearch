/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoCrossGramRowEnergy

/-!
# Prime-only factorial refinements and exact raw arithmetic cancellation

Source: continuation of the user-provided Pareto capacity handoff
(2026-09-21). The argument combines the proved Euler-factor formula,
orthogonal refinement identity, and exact coprime-certificate observations.

Composite refinement columns vanish. On prime rows, the raw tail-atom
matrix has explicit negative strict-lower entries and a positive diagonal.
Its complete row sum divided by that diagonal tends to zero along primes.
These unconditional raw formulas do not identify the screened innovation
matrix: nonsummability of the screened row energy remains Open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.Pareto.IntegerDPP

theorem factorialPrimeRefinement_energy (n : ℕ) :
    ‖factorialPrimeRefinement n‖ ^ 2 =
      ‖infiniteCoprimeCertificate (n+3).factorial‖ ^ 2 -
      ‖infiniteCoprimeCertificate (n+2).factorial‖ ^ 2 := by
  have h := infiniteCoprimeCertificate_refinement_energy
    (P := (n+2).factorial) (Q := (n+3).factorial)
    (Nat.factorial_ne_zero _) (Nat.dvd_factorial (by decide) (by omega))
    (Nat.factorial_ne_zero _) (Nat.factorial_dvd_factorial (by omega))
  change _ = _ + ‖factorialPrimeRefinement n‖ ^ 2 at h
  linarith

theorem factorialPrimeRefinement_eq_zero_of_not_prime (n : ℕ)
    (hn : ¬ Nat.Prime (n+3)) : factorialPrimeRefinement n = 0 := by
  have hf : (n+3).factorial.primeFactors = (n+2).factorial.primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hd, _⟩
      have hle := hp.dvd_factorial.mp hd
      have hne : p ≠ n+3 := by
        rintro rfl
        exact hn hp
      exact ⟨hp, hp.dvd_factorial.mpr (by omega), Nat.factorial_ne_zero _⟩
    · rintro ⟨hp, hd, _⟩
      exact ⟨hp, dvd_trans hd (Nat.factorial_dvd_factorial (by omega)), Nat.factorial_ne_zero _⟩
  have hm : coprimeReciprocalSquareMass (n+3).factorial =
      coprimeReciprocalSquareMass (n+2).factorial := by
    rw [coprimeReciprocalSquareMass_eulerProduct _ (Nat.factorial_ne_zero _)
        (Nat.dvd_factorial (by decide) (by omega)),
      coprimeReciprocalSquareMass_eulerProduct _ (Nat.factorial_ne_zero _)
        (Nat.dvd_factorial (by decide) (by omega)), hf]
  have hz : ‖factorialPrimeRefinement n‖ ^ 2 = 0 := by
    rw [factorialPrimeRefinement_energy,
      infiniteCoprimeCertificate_norm_sq _ (Nat.factorial_ne_zero _)
        (Nat.dvd_factorial (by decide) (by omega)),
      infiniteCoprimeCertificate_norm_sq _ (Nat.factorial_ne_zero _)
        (Nat.dvd_factorial (by decide) (by omega)), hm, sub_self]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

theorem factorialPrimeRefinement_ne_zero_iff (n : ℕ) :
    factorialPrimeRefinement n ≠ 0 ↔ Nat.Prime (n+3) := by
  constructor
  · exact fun h => Classical.byContradiction
      (fun hn => h (factorialPrimeRefinement_eq_zero_of_not_prime n hn))
  · intro hp hz
    have h := tailInnovation_inner_factorialPrimeRefinement n hp
    rw [hz, inner_zero_right] at h
    exact (ne_of_gt (factorialPrimeDelta_pos n)) h.symm

theorem factorialPrimeCrossGram_eq_zero_of_not_prime (n m : ℕ)
    (hm : ¬ Nat.Prime (m+3)) : factorialPrimeCrossGram n m = 0 := by
  simp [factorialPrimeCrossGram, factorialPrimeRefinement_eq_zero_of_not_prime m hm]

theorem factorialCrossGramRow_eq_prime_sum (n : ℕ) :
    factorialCrossGramRow n =
      ∑ j ∈ (Finset.range (n+1)).filter (fun j => Nat.Prime (j+3)),
        factorialPrimeCrossGram n j := by
  classical
  unfold factorialCrossGramRow
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hnot
  have hp : ¬ Nat.Prime (j+3) := by
    intro hp
    exact hnot (Finset.mem_filter.mpr ⟨hj, hp⟩)
  exact factorialPrimeCrossGram_eq_zero_of_not_prime n j hp

/-- The exact unscreened pairing at a later prime; the negative sign is arithmetic. -/
theorem tailAtom_inner_factorialPrimeRefinement_of_lt
    (n m : ℕ) (hn : Nat.Prime (n+3)) (hmn : m < n) :
    inner ℝ (tailAtom (n+1)) (factorialPrimeRefinement m) =
      - ‖factorialPrimeRefinement m‖ ^ 2 / (2 * ((n+3 : ℕ) : ℝ)^2) := by
  have hq : Nat.Prime ((n+1)+2) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using hn
  have hnew : ¬ ((n+1)+2) ∣ (m+3).factorial := by
    intro hd
    have h := hq.dvd_factorial.mp hd
    omega
  have hold : ¬ ((n+1)+2) ∣ (m+2).factorial := by
    intro hd
    have h := hq.dvd_factorial.mp hd
    omega
  change inner ℝ (tailAtom (n+1))
    (infiniteCoprimeCertificate (m+3).factorial -
      infiniteCoprimeCertificate (m+2).factorial) = _
  rw [inner_sub_right,
    infiniteCoprimeCertificate_fresh_prime_observation _ _ (Nat.factorial_ne_zero _)
      (Nat.dvd_factorial (by decide) (by omega)) hq hnew,
    infiniteCoprimeCertificate_fresh_prime_observation _ _ (Nat.factorial_ne_zero _)
      (Nat.dvd_factorial (by decide) (by omega)) hq hold,
    coprimePrimeDefect_energy_identity _ _ (Nat.factorial_ne_zero _)
      (Nat.dvd_factorial (by decide) (by omega)),
    coprimePrimeDefect_energy_identity _ _ (Nat.factorial_ne_zero _)
      (Nat.dvd_factorial (by decide) (by omega)),
    factorialPrimeRefinement_energy]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  ring

theorem tailAtom_inner_factorialPrimeRefinement_neg
    (n m : ℕ) (hn : Nat.Prime (n+3)) (hm : Nat.Prime (m+3)) (hmn : m < n) :
    inner ℝ (tailAtom (n+1)) (factorialPrimeRefinement m) < 0 := by
  rw [tailAtom_inner_factorialPrimeRefinement_of_lt n m hn hmn]
  exact div_neg_of_neg_of_pos
    (neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr
      ((factorialPrimeRefinement_ne_zero_iff m).mpr hm))))
    (by positivity)

/-- Exact source-to-refinement energy ratio at a prime stage. -/
theorem factorialPrimeRefinement_energy_eq_delta_mul (n : ℕ)
    (hn : Nat.Prime (n+3)) :
    ‖factorialPrimeRefinement n‖ ^ 2 =
      factorialPrimeDelta n * ‖infiniteCoprimeCertificate (n+3).factorial‖ ^ 2 := by
  have h2 : 2 ∣ (n+2).factorial := Nat.dvd_factorial (by decide) (by omega)
  have h3 : 2 ∣ (n+3).factorial := Nat.dvd_factorial (by decide) (by omega)
  have hnd : ¬ (n+3) ∣ (n+2).factorial := by
    intro hd
    have h := hn.dvd_factorial.mp hd
    omega
  have he : (n+3).factorial = (n+2).factorial * (n+3) := by
    rw [show n+3 = (n+2)+1 by omega, Nat.factorial_succ, mul_comm]
  have hm := coprimeReciprocalSquareMass_mul_fresh_prime (n+2).factorial
    (n+3) (Nat.factorial_ne_zero _) h2 hn hnd
  rw [← he] at hm
  have hs : coprimeReciprocalSquareMass (n+2).factorial - 1 ≠ 0 := by
    simpa only [coprimeReciprocalSquareMass, add_sub_cancel_left] using
      ne_of_gt (coprimePairMass_tsum_pos _ (Nat.factorial_ne_zero _) h2)
  have ht : coprimeReciprocalSquareMass (n+3).factorial - 1 ≠ 0 := by
    simpa only [coprimeReciprocalSquareMass, add_sub_cancel_left] using
      ne_of_gt (coprimePairMass_tsum_pos _ (Nat.factorial_ne_zero _) h3)
  have hq : ((n+3 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [factorialPrimeRefinement_energy,
    infiniteCoprimeCertificate_norm_sq _ (Nat.factorial_ne_zero _) h3,
    infiniteCoprimeCertificate_norm_sq _ (Nat.factorial_ne_zero _) h2]
  unfold factorialPrimeDelta coprimePrimeDefect
  field_simp [hs, ht, hq]
  have hm' : coprimeReciprocalSquareMass (n+3).factorial * ((n+3 : ℕ) : ℝ)^2 =
      coprimeReciprocalSquareMass (n+2).factorial * (((n+3 : ℕ) : ℝ)^2 - 1) := by
    rw [hm]
    field_simp
  nlinarith

/-- Before screening, the complete signed prime row has a closed formula. -/
theorem tailAtom_factorialRefinement_row_sum (n : ℕ) (hn : Nat.Prime (n+3)) :
    (∑ m ∈ Finset.range (n+1),
      inner ℝ (tailAtom (n+1)) (factorialPrimeRefinement m)) =
      coprimePrimeDefect (Nat.factorial 2) (n+3) := by
  have htel := factorialCoprimeCertificate_eq_base_add_refinements (n+1)
  have hi := congrArg (fun x => inner ℝ (tailAtom (n+1)) x) htel
  simp only [inner_add_right, inner_sum, Nat.add_assoc] at hi
  have hz := infiniteCoprimeCertificate_observation (n+2) (n+3).factorial
    (Nat.factorial_ne_zero _) (Nat.dvd_factorial (by decide) (by omega))
    (fun i => Nat.dvd_factorial (by omega) (by omega)) (Fin.last (n+1))
  simp only [Fin.val_last, reciprocalSource] at hz
  have hp : Nat.Prime ((n+1)+2) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using hn
  have hnd : ¬ ((n+1)+2) ∣ Nat.factorial 2 := by
    intro hd
    have h := hp.dvd_factorial.mp hd
    omega
  have hb := infiniteCoprimeCertificate_fresh_prime_observation (Nat.factorial 2)
    (n+1) (Nat.factorial_ne_zero _) (by decide) hp hnd
  simp only [Nat.add_assoc, Nat.reduceAdd] at hz hb
  rw [hz, hb] at hi
  linear_combination -hi

/-- The unscreened row divided by its positive prime diagonal tends to zero
along prime stages, with the following exact expression. -/
theorem tailAtom_factorialRefinement_row_ratio (n : ℕ) (hn : Nat.Prime (n+3)) :
    (∑ m ∈ Finset.range (n+1),
      inner ℝ (tailAtom (n+1)) (factorialPrimeRefinement m)) / factorialPrimeDelta n =
      (‖infiniteCoprimeCertificate (Nat.factorial 2)‖ ^ 2 + 2) /
        (‖infiniteCoprimeCertificate (n+2).factorial‖ ^ 2 + 2) := by
  rw [tailAtom_factorialRefinement_row_sum n hn, factorialPrimeDelta,
    coprimePrimeDefect_energy_identity _ _ (Nat.factorial_ne_zero _) (by decide),
    coprimePrimeDefect_energy_identity _ _ (Nat.factorial_ne_zero _)
      (Nat.dvd_factorial (by decide) (by omega))]
  have hq : ((n+3 : ℕ) : ℝ) ≠ 0 := by positivity
  have he : ‖infiniteCoprimeCertificate (n+2).factorial‖ ^ 2 + 2 ≠ 0 := by positivity
  have he' : 1 + ‖infiniteCoprimeCertificate (n+2).factorial‖ ^ 2 / 2 ≠ 0 := by positivity
  field_simp [hq, he, he']
  ring

theorem factorialRefinement_raw_cancellation_ratio_tendsto :
    Filter.Tendsto (fun n : ℕ =>
      (‖infiniteCoprimeCertificate (Nat.factorial 2)‖ ^ 2 + 2) /
        (‖infiniteCoprimeCertificate (n+2).factorial‖ ^ 2 + 2))
      Filter.atTop (nhds 0) := by
  have hE : Filter.Tendsto
      (fun n : ℕ => ‖infiniteCoprimeCertificate (n+2).factorial‖ ^ 2 + 2)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => by linarith)
      infiniteCoprimeCertificate_factorial_energy_tendsto
  simpa only [Function.comp_apply, mul_zero, div_eq_mul_inv] using
    (tendsto_const_nhds (x := ‖infiniteCoprimeCertificate (Nat.factorial 2)‖ ^ 2 + 2)).mul
      (tendsto_inv_atTop_zero.comp hE)

/-- Complete raw arithmetic matrix on prime rows, including every signed entry. -/
theorem tailAtom_factorialPrimeRefinement_prime_row (n m : ℕ)
    (hn : Nat.Prime (n+3)) :
    inner ℝ (tailAtom (n+1)) (factorialPrimeRefinement m) =
      if n < m then 0 else if n = m then factorialPrimeDelta n
      else - ‖factorialPrimeRefinement m‖ ^ 2 / (2 * ((n+3 : ℕ) : ℝ)^2) := by
  by_cases hlt : n < m
  · rw [if_pos hlt]
    exact factorialPrimeRefinement_old_observation_zero m ⟨n+1, by omega⟩
  · rw [if_neg hlt]
    by_cases he : n = m
    · subst m
      rw [if_pos rfl]
      exact tailAtom_inner_factorialPrimeRefinement n hn
    · rw [if_neg he]
      exact tailAtom_inner_factorialPrimeRefinement_of_lt n m hn (by omega)

/-- Actual raw row ratios converge to zero when restricted to prime stages. -/
theorem tailAtom_factorialRefinement_prime_row_ratio_tendsto :
    Filter.Tendsto (fun n : ℕ =>
      (∑ m ∈ Finset.range (n+1),
        inner ℝ (tailAtom (n+1)) (factorialPrimeRefinement m)) / factorialPrimeDelta n)
      (Filter.atTop ⊓ Filter.principal {n : ℕ | Nat.Prime (n+3)}) (nhds 0) := by
  apply (factorialRefinement_raw_cancellation_ratio_tendsto.mono_left inf_le_left).congr'
  exact Filter.eventually_inf_principal.mpr
    (Filter.Eventually.of_forall (fun n hn =>
      (tailAtom_factorialRefinement_row_ratio n hn).symm))

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
