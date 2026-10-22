/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoBalancedSchurTrial
import RiemannResearch.RH.ParetoAdjacentMomentCorrection

/-!
# Harmonic adjacent-row bounds for the actual Schur pivot

Source: an independently derived assembly of the repository's exact
adjacent-residue energy and actual finite inverse-Gram completion.
The entire first-period energy and literal infinite remainder are retained.
This gives a stronger pointwise gain certificate, not a divergence provider.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization CoefficientStabilization.TailCapacity

def adjacentSchurTrial (n : ℕ) : ThresholdHilbert :=
  tailAtom (n + 1) -
    (((n + 2 : ℕ) : ℝ) / ((n + 3 : ℕ) : ℝ)) • tailAtom n

theorem adjacentSchurTrial_eq_packet (n : ℕ) :
    adjacentSchurTrial n =
      (-(1 / (((n + 2 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)))) •
        adjacentMomentPacket n := by
  unfold adjacentSchurTrial adjacentMomentPacket
  rw [smul_sub, smul_smul, smul_smul]
  have hd : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hq : ((n + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  have h₁ : -(1 / (((n + 2 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ))) *
      ((n + 2 : ℕ) : ℝ) ^ 2 =
      -(((n + 2 : ℕ) : ℝ) / ((n + 3 : ℕ) : ℝ)) := by
    field_simp [hd, hq]
    <;> ring
  have h₂ : -(1 / (((n + 2 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ))) *
      (((n + 2 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)) = -1 := by
    field_simp [hd, hq]
  rw [h₁, h₂]
  simp only [neg_smul, one_smul]
  abel

/-- Exact whole-tail energy before any upper bound is applied. -/
theorem adjacentSchurTrial_norm_sq_exact (n : ℕ) :
    ‖adjacentSchurTrial n‖ ^ 2 =
      ((harmonic (n + 2) : ℝ) -
        ((n + 2 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ) + 1) +
        adjacentResidueRemainder (n + 2)) / ((n + 3 : ℕ) : ℝ) ^ 2 := by
  rw [adjacentSchurTrial_eq_packet, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, adjacentMomentPacket_harmonic_exact]
  have hd : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hq : ((n + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem adjacentSchurTrial_norm_sq_le_harmonic (n : ℕ) :
    ‖adjacentSchurTrial n‖ ^ 2 ≤
      (harmonic (n + 2) : ℝ) / ((n + 3 : ℕ) : ℝ) ^ 2 := by
  rw [adjacentSchurTrial_norm_sq_exact]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  linarith [adjacentResidueRemainder_le (n + 2) (by omega)]

theorem schurSigma_le_adjacent_harmonic (n : ℕ) :
    schurSigma (n + 1) ≤
      (harmonic (n + 2) : ℝ) / ((n + 3 : ℕ) : ℝ) ^ 2 := by
  have h := schurSigma_le_balancedTrial_norm_sq (n + 1)
    (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
    (((n + 2 : ℕ) : ℝ) / ((n + 3 : ℕ) : ℝ))
  exact h.trans (adjacentSchurTrial_norm_sq_le_harmonic n)

theorem schurEta_eq_neg_adjacentTrial (n : ℕ) :
    schurEta (n + 1) =
      -inner ℝ (adjacentSchurTrial n) (tailMinimum (n + 1)) := by
  apply schurEta_eq_neg_balancedTrial (n + 1)
    (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
    (((n + 2 : ℕ) : ℝ) / ((n + 3 : ℕ) : ℝ))
  change (((n + 2 : ℕ) : ℝ) / ((n + 3 : ℕ) : ℝ)) *
    (1 / ((n + 2 : ℕ) : ℝ)) = 1 / ((n + 1 + 2 : ℕ) : ℝ)
  rw [show n + 1 + 2 = n + 3 by omega]
  field_simp

theorem schurGain_ge_adjacent_harmonic (n : ℕ) :
    (schurEta (n + 1)) ^ 2 /
        ((harmonic (n + 2) : ℝ) / ((n + 3 : ℕ) : ℝ) ^ 2) ≤
      (schurEta (n + 1)) ^ 2 / schurSigma (n + 1) := by
  have hs := schurSigma_le_adjacent_harmonic n
  have hK := (schurSigma_pos (n + 1)).trans_le hs
  apply (div_le_div_iff₀ hK (schurSigma_pos (n + 1))).mpr
  exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)

theorem factorialPrimeGain_ge_adjacent_harmonic
    (n : ℕ) (hp : Nat.Prime (n + 3)) :
    (schurEta (n + 1)) ^ 2 /
        ((harmonic (n + 2) : ℝ) / ((n + 3 : ℕ) : ℝ) ^ 2) ≤
      factorialPrimeGain n := by
  rw [factorialPrimeGain, if_pos hp]
  exact schurGain_ge_adjacent_harmonic n

theorem factorialCompositeGain_ge_adjacent_harmonic
    (n : ℕ) (hp : ¬ Nat.Prime (n + 3)) :
    (schurEta (n + 1)) ^ 2 /
        ((harmonic (n + 2) : ℝ) / ((n + 3 : ℕ) : ℝ) ^ 2) ≤
      factorialCompositeGain n := by
  rw [factorialCompositeGain, if_neg hp]
  exact schurGain_ge_adjacent_harmonic n

def adjacentInnovationLower (n : ℕ) : ℝ :=
  (schurEta (n + 1)) ^ 2 /
    ((harmonic (n + 2) : ℝ) / ((n + 3 : ℕ) : ℝ) ^ 2)

theorem adjacentInnovationLower_nonneg (n : ℕ) :
    0 ≤ adjacentInnovationLower n := by
  unfold adjacentInnovationLower
  exact div_nonneg (sq_nonneg _)
    ((schurSigma_pos (n + 1)).trans_le (schurSigma_le_adjacent_harmonic n)).le

theorem adjacentInnovationLower_le_prime_add_composite (n : ℕ) :
    adjacentInnovationLower n ≤ factorialPrimeGain n + factorialCompositeGain n := by
  unfold adjacentInnovationLower
  by_cases hp : Nat.Prime (n + 3) <;>
    simpa [factorialPrimeGain, factorialCompositeGain, hp] using
      schurGain_ge_adjacent_harmonic n

/-- Every actual conductor contributes; the initial capacity is retained. -/
theorem adjacentInnovationLower_sum_le_capacity (N : ℕ) :
    (∑ n ∈ Finset.range N, adjacentInnovationLower n) ≤
      tailCapacity (N + 1) - tailCapacity 1 := by
  have hs := Finset.sum_le_sum (s := Finset.range N)
    (fun n _ => adjacentInnovationLower_le_prime_add_composite n)
  have hs' : (∑ n ∈ Finset.range N, adjacentInnovationLower n) ≤
      primeGainBudget N + compositeGainBudget N := by
    simpa only [Finset.sum_add_distrib, primeGainBudget, compositeGainBudget] using hs
  linarith [capacity_eq_prime_composite_budget N]

/-- A stronger unconditional pointwise source bound. The actual gain still
contains its complete signed screened correction. -/
theorem factorialPrimeSourceEnergy_ge_adjacent_harmonic
    (n : ℕ) (hp : Nat.Prime (n + 3)) :
    1 / (4 * (harmonic (n + 2) : ℝ)) ≤ factorialPrimeSourceEnergy n := by
  have hs := schurSigma_le_adjacent_harmonic n
  have hK := (schurSigma_pos (n + 1)).trans_le hs
  have hH : (harmonic (n + 2) : ℝ) ≠ 0 := by
    intro he
    simp only [he, zero_div] at hK
    exact lt_irrefl 0 hK
  have hq : ((n + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd : 1 / (2 * ((n + 3 : ℕ) : ℝ)) ≤
      coprimePrimeDefect (n + 2).factorial (n + 3) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      factorialPrimeDefect_lower (n + 1) (by omega)
  have hd2 := pow_le_pow_left₀ (by positivity) hd 2
  rw [factorialPrimeSourceEnergy, if_pos hp]
  calc
    1 / (4 * (harmonic (n + 2) : ℝ)) =
        (1 / (2 * ((n + 3 : ℕ) : ℝ))) ^ 2 /
          ((harmonic (n + 2) : ℝ) / ((n + 3 : ℕ) : ℝ) ^ 2) := by
      field_simp [hH, hq]
      <;> ring
    _ ≤ (coprimePrimeDefect (n + 2).factorial (n + 3)) ^ 2 /
        ((harmonic (n + 2) : ℝ) / ((n + 3 : ℕ) : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right hd2 hK.le
    _ ≤ (coprimePrimeDefect (n + 2).factorial (n + 3)) ^ 2 / schurSigma (n + 1) := by
      apply (div_le_div_iff₀ hK (schurSigma_pos (n + 1))).mpr
      exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)

end RiemannResearch.RH.Pareto.IntegerDPP
