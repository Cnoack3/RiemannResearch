/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeDerivativePeriodMean
import RiemannResearch.LinearAlgebra.DerivativeOptimizerPeriodMean
import RiemannResearch.NumberTheory.PrimeProductEnergyGrowth

/-!
# Unconditional full Q-energy divergence of the derivative-optimal primitives

The finite prime-product primitive is an actual legal squarefree residue sum.
Its exact period mean forces a lower bound for its entire Q-Hilbert norm.
Along the first primes that lower bound diverges.  Thus the unregularized
derivative minimizers do not furnish the bounded-energy lift needed for RH.
No assertion about arbitrary legal approximants follows from this no-go result.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QPrimeDerivativeEnergyNoGo
open ZetaTwoProbability ZetaTwoHilbert ArithmeticCumulative
open QPrimeDerivativePrimitive QPrimeDerivativePeriodMean
open RiemannResearch.LinearAlgebra.DerivativeOptimizerPeriodMean
open RiemannResearch.NumberTheory.PrimeProductEnergyGrowth

theorem sum_successor_squares_le_cube (L : ℕ) :
    (∑ k ∈ Finset.range L, ((k+1:ℕ):ℝ)^2) ≤ (L:ℝ)^3 := by
  calc
    _ ≤ ∑ _k ∈ Finset.range L, (L:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN : k+1 ≤ L := by
        have hh := Finset.mem_range.mp hk
        omega
      have hkR : ((k+1:ℕ):ℝ) ≤ (L:ℝ) := by exact_mod_cast hkN
      have hprod := mul_nonneg
        (sub_nonneg.mpr hkR)
        (show 0 ≤ (L:ℝ)+((k+1:ℕ):ℝ) by positivity)
      nlinarith
    _ = _ := by simp; ring

theorem q_prefix_energy_le_norm_sq (f : QHilbert) (L : ℕ) :
    (1/zetaTwo)*(∑ k ∈ Finset.range L,
      (qSequence f (k+1))^2/((k+1:ℕ):ℝ)^2) ≤ ‖f‖^2 := by
  calc
    _ = ∑ k ∈ Finset.range L,
        positiveQWeight (k+1)*(qSequence f (k+1))^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [positiveQWeight, div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    _ = ∑ k ∈ Finset.range L, (f k)^2 := by
      simp_rw [qSequence_weighted_square]
    _ ≤ ‖f‖^2 := by
      rw [qNorm_sq]
      exact (qCoordinate_square_summable f).sum_le_tsum _ (fun _ _ => sq_nonneg _)

/-- A nonzero exact cumulative mean forces a lower bound on the actual infinite
norm; the prefix-to-norm step uses the Q-Hilbert isometry. -/
theorem qNorm_sq_lower_of_cumulative_mean (f : QHilbert) (L : ℕ) (M : ℝ)
    (hL : 0 < L) (hM : 0 < M)
    (hmean : cumulative (qSequence f) L =
      (1/zetaTwo)*(L:ℝ)^2/(2*M)) :
    (1/zetaTwo)^3*(L:ℝ)/(4*M^2) ≤ ‖f‖^2 := by
  have hq : 0 < (1/zetaTwo:ℝ) := div_pos zero_lt_one zetaTwo_pos
  have hLR : (0:ℝ) < L := by exact_mod_cast hL
  have hs : (Finset.range L).Nonempty := by
    exact ⟨0, Finset.mem_range.mpr hL⟩
  have hfinite := weighted_energy_lower_from_period_mean
    (Finset.range L) hs (fun k => qSequence f (k+1))
    (fun k => ((k+1:ℕ):ℝ)^2) hq hLR hM
    (by intro k _; positivity)
    (by simpa only [cumulative] using hmean)
    (sum_successor_squares_le_cube L)
  exact hfinite.trans (q_prefix_energy_le_norm_sq f L)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact physical energy obstruction for every nonempty distinct-prime family.
There is no assumed period-mean or prefix-energy hypothesis in this theorem. -/
theorem primitive_norm_sq_lower [Nonempty ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (1/zetaTwo)^3*(fullPeriod p:ℝ)/
      (4*((2:ℝ)^(Fintype.card ι))^2) ≤ ‖primitive p‖^2 := by
  have hL : 0 < fullPeriod p :=
    Finset.prod_pos (fun i _ => (hp i).pos)
  exact qNorm_sq_lower_of_cumulative_mean (primitive p) (fullPeriod p)
    ((2:ℝ)^(Fintype.card ι)) hL (by positivity)
    (cumulative_primitive_period p hp hinj)

/-- We start with two primes so every stage has a nonempty Boolean cube. -/
def firstPrimes (n : ℕ) : Fin (n+2) → ℕ :=
  fun i => Nat.nth Nat.Prime i.val

theorem firstPrimes_prime (n : ℕ) (i : Fin (n+2)) :
    (firstPrimes n i).Prime := Nat.prime_nth_prime i.val

theorem firstPrimes_injective (n : ℕ) : Function.Injective (firstPrimes n) := by
  intro i j hij
  apply Fin.ext
  exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij

theorem fullPeriod_firstPrimes (n : ℕ) :
    fullPeriod (firstPrimes n) = ordinalPrimorial (n+2) := by
  exact Fin.prod_univ_eq_prod_range (Nat.nth Nat.Prime) (n+2)

def ordinalPrimitive (n : ℕ) : QHilbert := primitive (firstPrimes n)

theorem ordinalPrimitive_norm_sq_lower (n : ℕ) :
    ((1/zetaTwo)^3/4)*(ordinalPrimorial (n+2):ℝ)/
      ((2:ℝ)^(n+2))^2 ≤ ‖ordinalPrimitive n‖^2 := by
  have h := primitive_norm_sq_lower (firstPrimes n)
    (firstPrimes_prime n) (firstPrimes_injective n)
  rw [fullPeriod_firstPrimes] at h
  simp only [Fintype.card_fin] at h
  change ((1/zetaTwo)^3/4)*(ordinalPrimorial (n+2):ℝ)/
    ((2:ℝ)^(n+2))^2 ≤ ‖primitive (firstPrimes n)‖^2
  convert h using 1 <;> ring

/-- The actual complete energy of the explicit derivative-optimal legal
primitive diverges unconditionally; this is not merely a scalar criterion. -/
theorem ordinalPrimitive_norm_sq_tendsto_atTop :
    Tendsto (fun n => ‖ordinalPrimitive n‖^2) atTop atTop := by
  exact energy_tendsto_atTop_of_period_lower
    (c := (1/zetaTwo)^3/4)
    (fun n => ‖ordinalPrimitive n‖^2)
    (by have hz := zetaTwo_pos; positivity)
    ordinalPrimitive_norm_sq_lower

theorem ordinalPrimitive_no_uniform_energy_budget :
    ¬ ∃ C : ℝ, ∀ n, ‖ordinalPrimitive n‖^2 ≤ C := by
  exact no_uniform_energy_budget_of_period_lower
    (c := (1/zetaTwo)^3/4)
    (fun n => ‖ordinalPrimitive n‖^2)
    (by have hz := zetaTwo_pos; positivity)
    ordinalPrimitive_norm_sq_lower

end RiemannResearch.RH.QPrimeDerivativeEnergyNoGo
