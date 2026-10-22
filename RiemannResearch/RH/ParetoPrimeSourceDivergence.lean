/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoCoprimePrimeUpdates
import RiemannResearch.RH.ParetoCoprimeCertificateEscape
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Divergent normalized fresh-prime source energy

Source: continuation of the user-provided
ParetoCapacityFormalization20260921 (2).md (2026-09-21), especially its
fresh-prime decomposition. We prove bounds for the actual Pareto residue
norm and the full Schur complement, and combine the existing factorial
support-escape bound with the exact defect-energy identity.

The last divergence step uses Mathlib's formalized Erdos proof of divergence
of the prime reciprocal series, supporting that proof step:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/SumPrimeReciprocals.html

This is divergence of the explicit positive source energy. The actual
capacity numerator also contains a signed error, which is not discarded.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization CoefficientStabilization.TailCapacity
open IntegerDPP ArithmeticCumulative
open RiemannResearch.Analysis.FiniteHilbertGram

theorem normalizedResidue_coordinate_sq_le_inv_sq (d : ℕ) (hd : 0 < d) (k : ℕ) :
    (normalizedResidueHilbert d hd k) ^ 2 ≤ 1 / (d : ℝ) ^ 2 := by
  rw [← hilbertSequence_weighted_square, positiveWeight_succ,
    normalizedResidueHilbert_sequence]
  have hm : (↑((k + 1) % d) : ℝ) ≤ (k : ℝ) + 1 := by
    exact_mod_cast Nat.mod_le (k + 1) d
  have hm0 : (0 : ℝ) ≤ ↑((k + 1) % d) := Nat.cast_nonneg _
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hp : 0 < ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
  have hb : (↑((k + 1) % d) : ℝ) ^ 2 ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
    nlinarith
  calc
    _ = ((↑((k + 1) % d) : ℝ) ^ 2 /
        (((k : ℝ) + 1) * ((k : ℝ) + 2))) / (d : ℝ) ^ 2 := by
      simp only [paretoWeight, residueFraction]
      ring
    _ ≤ 1 / (d : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right ((div_le_one hp).mpr hb) (sq_nonneg _)

theorem normalizedResidue_coordinate_sq_le_weight (d : ℕ) (hd : 0 < d) (k : ℕ) :
    (normalizedResidueHilbert d hd k) ^ 2 ≤ paretoWeight k := by
  rw [← hilbertSequence_weighted_square, positiveWeight_succ,
    normalizedResidueHilbert_sequence]
  have hm : (↑((k + 1) % d) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (Nat.mod_lt (k + 1) hd).le
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hg : 0 ≤ residueFraction d (k + 1) := by unfold residueFraction; positivity
  have hg1 : residueFraction d (k + 1) ≤ 1 := (div_le_one hdR).mpr hm
  have hg2 : residueFraction d (k + 1) ^ 2 ≤ 1 := by nlinarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hg2 (paretoWeight_pos k).le

theorem normalizedResidue_norm_sq_le (d : ℕ) (hd : 0 < d) :
    ‖normalizedResidueHilbert d hd‖ ^ 2 ≤ 2 / (d : ℝ) := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have htail : (∑' n : ℕ, paretoWeight (n + d)) = 1 / ((d : ℝ) + 1) := by
    have h := paretoWeight_hasSum.summable.sum_add_tsum_nat_add d
    rw [paretoWeight_hasSum.tsum_eq, paretoWeight_partial_sum] at h
    linarith
  rw [hilbert_norm_sq,
    ← (hilbert_coordinate_square_summable (normalizedResidueHilbert d hd)).sum_add_tsum_nat_add d]
  have hh : (∑ k ∈ Finset.range d, (normalizedResidueHilbert d hd k) ^ 2) ≤
      (d : ℝ) * (1 / (d : ℝ) ^ 2) := by
    simpa using Finset.sum_le_sum (s := Finset.range d)
      (fun k _ => normalizedResidue_coordinate_sq_le_inv_sq d hd k)
  have ht : (∑' k, (normalizedResidueHilbert d hd (k + d)) ^ 2) ≤
      1 / ((d : ℝ) + 1) := by
    rw [← htail]
    exact Summable.tsum_le_tsum (fun k => normalizedResidue_coordinate_sq_le_weight d hd (k + d))
      ((summable_nat_add_iff d).mpr
        (hilbert_coordinate_square_summable (normalizedResidueHilbert d hd)))
      ((summable_nat_add_iff d).mpr paretoWeight_hasSum.summable)
  have hi : 1 / ((d : ℝ) + 1) ≤ 1 / (d : ℝ) :=
    one_div_le_one_div_of_le hdR (by linarith)
  have he : (d : ℝ) * (1 / (d : ℝ) ^ 2) = 1 / (d : ℝ) := by
    field_simp
  rw [he] at hh
  have he2 : 2 / (d : ℝ) = 1 / (d : ℝ) + 1 / (d : ℝ) := by ring
  linarith

namespace CoefficientStabilization.TailCapacity

theorem schurSigma_le_two_div (n : ℕ) :
    schurSigma n ≤ 2 / ((n + 2 : ℕ) : ℝ) := by
  have hp := residual_minimizes (finiteTailAtom_independent n) (tailAtom n) 0
  simp only [map_zero, sub_zero] at hp
  have ht : ‖tailAtom n‖ ^ 2 ≤ ‖residueAtom n‖ ^ 2 := by
    rw [tailAtom, tailMap_norm_sq]
    nlinarith [sq_nonneg (anchoredEvaluationCLM 1 (residueAtom n))]
  exact hp.trans (ht.trans (normalizedResidue_norm_sq_le (n + 2) (by omega)))

theorem coprimePrimeDefect_energy_identity (P q : ℕ) (hP : P ≠ 0) (h2 : 2 ∣ P) :
    coprimePrimeDefect P q = (1 + ‖infiniteCoprimeCertificate P‖ ^ 2 / 2) / (q : ℝ) ^ 2 := by
  have hS : coprimeReciprocalSquareMass P - 1 ≠ 0 := by
    simpa only [coprimeReciprocalSquareMass, add_sub_cancel_left] using
      ne_of_gt (coprimePairMass_tsum_pos P hP h2)
  rw [infiniteCoprimeCertificate_norm_sq P hP h2]
  unfold coprimePrimeDefect
  field_simp
  ring

theorem factorialPrimeDefect_lower (n : ℕ) (hn : 0 < n) :
    1 / (2 * ((n + 2 : ℕ) : ℝ)) ≤ coprimePrimeDefect (n + 1).factorial (n + 2) := by
  have h2 : 2 ∣ (n + 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  rw [coprimePrimeDefect_energy_identity _ _ (Nat.factorial_ne_zero _) h2]
  have he : (n : ℝ) + 1 ≤ ‖infiniteCoprimeCertificate (n + 1).factorial‖ ^ 2 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using infiniteCoprimeCertificate_factorial_energy_lower m
  have hq : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((n + 2 : ℕ) : ℝ))
    (sq_pos_of_pos hq)).mpr
  push_cast at *
  nlinarith

theorem factorialPrimeDefect_normalized_lower (n : ℕ) (hn : 0 < n) :
    1 / (8 * ((n + 2 : ℕ) : ℝ)) ≤
      (coprimePrimeDefect (n + 1).factorial (n + 2)) ^ 2 / schurSigma n := by
  have hd := factorialPrimeDefect_lower n hn
  have hs := schurSigma_le_two_div n
  have hq : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hd0 : 0 ≤ coprimePrimeDefect (n + 1).factorial (n + 2) :=
    (by positivity : (0 : ℝ) ≤ 1 / (2 * ((n + 2 : ℕ) : ℝ))).trans hd
  have hd2 : (1 / (2 * ((n + 2 : ℕ) : ℝ))) ^ 2 ≤
      (coprimePrimeDefect (n + 1).factorial (n + 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hd 2
  apply (le_div_iff₀ (schurSigma_pos n)).mpr
  calc
    _ ≤ (1 / (8 * ((n + 2 : ℕ) : ℝ))) * (2 / ((n + 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (1 / (2 * ((n + 2 : ℕ) : ℝ))) ^ 2 := by ring
    _ ≤ _ := hd2

end CoefficientStabilization.TailCapacity
end RiemannResearch.RH.Pareto
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.Pareto.IntegerDPP
/-- Only odd fresh-prime stages; n indexes dictionary size n+1. -/
def factorialPrimeSourceEnergy (n : ℕ) : ℝ :=
  if Nat.Prime (n + 3) then
    (coprimePrimeDefect (n + 2).factorial (n + 3)) ^ 2 / schurSigma (n + 1)
  else 0

theorem factorialPrimeSourceEnergy_nonneg (n : ℕ) : 0 ≤ factorialPrimeSourceEnergy n := by
  unfold factorialPrimeSourceEnergy
  split_ifs
  · exact div_nonneg (sq_nonneg _) (schurSigma_pos _).le
  · exact le_rfl

theorem factorialPrimeSourceEnergy_not_summable :
    ¬ Summable factorialPrimeSourceEnergy := by
  intro hs
  have hl (n : ℕ) :
      (if Nat.Prime (n + 3) then 1 / ((n + 3 : ℕ) : ℝ) else 0) ≤
        8 * factorialPrimeSourceEnergy n := by
    by_cases hp : Nat.Prime (n + 3)
    · simp only [factorialPrimeSourceEnergy, if_pos hp]
      have h := factorialPrimeDefect_normalized_lower (n + 1) (by omega)
      simp only [Nat.add_assoc, Nat.reduceAdd] at h
      have he : 1 / (8 * ((n + 3 : ℕ) : ℝ)) =
          (1 / ((n + 3 : ℕ) : ℝ)) / 8 := by ring
      rw [he] at h
      linarith
    · simp only [factorialPrimeSourceEnergy, if_neg hp, mul_zero, le_refl]
  have hh : Summable (fun n : ℕ =>
      if Nat.Prime (n + 3) then 1 / ((n + 3 : ℕ) : ℝ) else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hl (hs.mul_left 8)
  apply not_summable_one_div_on_primes
  apply (summable_nat_add_iff 3).mp
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hh

theorem factorialPrimeSourceEnergy_sum_tendsto :
    Tendsto (fun N => ∑ n ∈ Finset.range N, factorialPrimeSourceEnergy n) atTop atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg factorialPrimeSourceEnergy_nonneg).mp
    factorialPrimeSourceEnergy_not_summable


end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
