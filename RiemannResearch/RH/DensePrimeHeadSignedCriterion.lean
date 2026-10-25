/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ActualPrimeHeadSignedCriterion
import RiemannResearch.RH.ParetoAmplitudeCertificates
import RiemannResearch.RH.PrimeHeadRefinedCertificates
import RiemannResearch.RH.QPrimeBalancedExactHead
import RiemannResearch.RH.SquarefreeSignedCorrelationCriterion
import RiemannResearch.RH.SquarefreePrimeHeadStage
import RiemannResearch.Analysis.SignedEnergyAverages
import RiemannResearch.Analysis.NormalizedSignedEnergy
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Dense prime-balanced heads retain reciprocal certificate mass

Source: the user's signed-weight/selector proposal, 24 October 2026.
Bertrand's postulate bounds the least prime anchor by 2N. The complete
P error is at most 9N, and refined unit certificates are at most 18N.
Consequently reciprocal certificate mass diverges for all consecutive
heads N=j + 1. Only signed correlation decay remains in the RH consumer.
This says nothing about mass retention after the geometric sparse selector.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QPrimeBalancedExactHead
open Pareto Pareto.AmplitudeCertificates RiemannResearch.Analysis

theorem anchorPrime_le_two_mul (N : ℕ) (hN : 0 < N) :
    anchorPrime N ≤ 2*N := by
  obtain ⟨p, hp, hNp, hpN⟩ :=
    Nat.exists_prime_lt_and_le_two_mul N (Nat.ne_of_gt hN)
  have hmin : anchorPrime N ≤ p := by
    change Nat.find (Nat.exists_infinite_primes (N + 1)) ≤ p
    exact Nat.find_min' _ ⟨by omega, hp⟩
  exact hmin.trans hpN

theorem nextPrimeResidual_head_zero (N : ℕ) :
    head (nextPrimeResidual N) N = 0 := by
  unfold head
  apply Finset.sum_eq_zero
  intro n hn
  have hnN : n + 1 ≤ N := by have := Finset.mem_range.mp hn; omega
  simp only [nextPrimeResidual, nextPrimeHead_exact N (n + 1) (by omega) hnN,
    sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]

/-- Unconditional complete energy bound along every positive physical head. -/
theorem nextPrimeResidual_energy_le_nine_mul (N : ℕ) (hN : 0 < N) :
    energy (nextPrimeResidual N) ≤ 9*(N : ℝ) := by
  have hb := certificate_bounds (nextPrimeResidual N) (N + anchorPrime N : ℕ)
    (Nat.cast_nonneg _) (fun n => nextPrimeHead_amplitude N (n + 1) hN) N
  rw [certificate, nextPrimeResidual_head_zero, zero_add] at hb
  have hanchor := anchorPrime_le_two_mul N hN
  have hU : ((N + anchorPrime N : ℕ) : ℝ) ≤ 3*(N : ℝ) := by
    exact_mod_cast (show N + anchorPrime N ≤ 3*N by omega)
  have hUsq : (((N + anchorPrime N : ℕ) : ℝ))^2 ≤ (3*(N : ℝ))^2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr hU
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  apply hb.1.trans
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ)+1)).mpr
  nlinarith

theorem nextPrimeCertificate_le_eighteen_mul (N : ℕ) (hN : 0 < N) :
    nextPrimeCertificate N ≤ 18*(N : ℝ) := by
  have hE := nextPrimeResidual_energy_le_nine_mul N hN
  rw [nextPrimeResidual_energy_eq] at hE
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hm : max 1 (‖hilbertOne - paretoNextPrimeHead N‖ ^ 2) ≤ 9*(N : ℝ) :=
    max_le (by linarith) hE
  have hb := (nextPrimeCertificate_bounds N hN).2
  linarith

/-- The simple energy bounds give exactly harmonic reciprocal mass. -/
theorem dense_linear_mass_eq (m : ℕ) :
    (∑ j ∈ Finset.range m, (9 * ((j + 1 : ℕ) : ℝ))⁻¹) =
      (9 : ℝ)⁻¹ * ∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ℝ))⁻¹ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_inv_rev, mul_comm]

/-- The normalized linear-certificate weights are exactly harmonic weights. -/
theorem dense_reciprocalEnergyAverage_eq_harmonic (m : ℕ) :
    reciprocalEnergyAverage (fun j => paretoNextPrimeHead (j + 1))
      (fun j => 9 * ((j + 1 : ℕ) : ℝ)) m =
    (∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ℝ))⁻¹)⁻¹ •
      (∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ℝ))⁻¹ • paretoNextPrimeHead (j + 1)) := by
  unfold reciprocalEnergyAverage
  rw [dense_linear_mass_eq, mul_inv_rev, inv_inv]
  have hsum :
      (∑ j ∈ Finset.range m, (9 * ((j + 1 : ℕ) : ℝ))⁻¹ • paretoNextPrimeHead (j + 1)) =
      (9 : ℝ)⁻¹ • (∑ j ∈ Finset.range m,
        (((j + 1 : ℕ) : ℝ))⁻¹ • paretoNextPrimeHead (j + 1)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [smul_smul, mul_inv_rev, mul_comm]
  rw [hsum, smul_smul, mul_assoc,
    mul_inv_cancel₀ (by norm_num : (9 : ℝ) ≠ 0), mul_one]

theorem dense_linear_reciprocal_not_summable :
    ¬ Summable (fun j : ℕ => (9 * ((j + 1 : ℕ) : ℝ))⁻¹) := by
  intro hs
  have hshift : Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ))⁻¹) := by
    apply (hs.mul_left (9 : ℝ)).congr
    intro j
    (norm_num [mul_inv_rev]; ring)
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp hshift)

theorem dense_linear_mass_tendsto :
    Tendsto (fun m : ℕ => ∑ j ∈ Finset.range m, (9 * ((j + 1 : ℕ) : ℝ))⁻¹)
      atTop atTop := by
  classical
  by_contra h
  apply dense_linear_reciprocal_not_summable
  have hn (j : ℕ) : 0 ≤ (9 * ((j + 1 : ℕ) : ℝ))⁻¹ := by positivity
  exact (summable_iff_not_tendsto_nat_atTop_of_nonneg hn).mpr h

/-- With A_N=9N, the normalized weighted average uses the fixed harmonic
weights 1/N. The entire diagonal is at most 9/H_M. -/
theorem dense_linear_diagonal_le (m : ℕ) :
    reciprocalEnergyDiagonal (fun j => paretoNextPrimeHead (j + 1) - hilbertOne)
      (fun j => 9 * ((j + 1 : ℕ) : ℝ)) m ≤
        9 * (∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ℝ))⁻¹)⁻¹ := by
  have he (j : ℕ) : ‖paretoNextPrimeHead (j + 1) - hilbertOne‖^2 ≤
      9 * ((j + 1 : ℕ) : ℝ) := by
    rw [norm_sub_rev, ← nextPrimeResidual_energy_eq]
    exact nextPrimeResidual_energy_le_nine_mul (j + 1) (by omega)
  have hd := reciprocalEnergyDiagonal_le_mass_inv
    (fun j => paretoNextPrimeHead (j + 1) - hilbertOne)
    (fun j => 9 * ((j + 1 : ℕ) : ℝ)) (fun j => by positivity) he m
  rw [dense_linear_mass_eq, mul_inv_rev, inv_inv] at hd
  simpa only [mul_comm] using hd

/-- The concrete harmonic-weight route to RH has only the actual normalized
signed correlation budget as its remaining asymptotic input. -/
theorem riemannHypothesis_of_dense_harmonic_cross_budget (b : ℕ → ℝ)
    (hcross : ∀ᶠ m in atTop,
      reciprocalEnergyCross (fun j => paretoNextPrimeHead (j + 1) - hilbertOne)
        (fun j => 9 * ((j + 1 : ℕ) : ℝ)) m ≤ b m)
    (hbudget : Tendsto b atTop (𝓝 0)) : RiemannHypothesis := by
  have hstage : Monotone (fun j => anchorPrime (j + 1)-1) := by
    intro i j hij
    exact Nat.sub_le_sub_right (anchorPrime_monotone (Nat.add_le_add_right hij 1)) 1
  have he (j : ℕ) : ‖paretoNextPrimeHead (j + 1) - hilbertOne‖^2 ≤
      9 * ((j + 1 : ℕ) : ℝ) := by
    rw [norm_sub_rev, ← nextPrimeResidual_energy_eq]
    exact nextPrimeResidual_energy_le_nine_mul (j + 1) (by omega)
  exact SquarefreePacketCapacity.riemannHypothesis_of_signed_correlation_budget
    (fun j => anchorPrime (j + 1)-1) hstage (fun j => paretoNextPrimeHead (j + 1))
    (fun j => SquarefreePacketCapacity.paretoNextPrimeHead_mem_stage (j + 1))
    (fun j => 9 * ((j + 1 : ℕ) : ℝ)) (fun j => by positivity) he b hcross hbudget
    dense_linear_mass_tendsto

/-- Consecutive heads avoid the reciprocal-mass loss of sparse selection. -/
theorem dense_nextPrimeCertificate_reciprocal_not_summable :
    ¬ Summable (fun j : ℕ => (nextPrimeCertificate (j + 1))⁻¹) := by
  intro hs
  have hshift : Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ))⁻¹) := by
    apply Summable.of_nonneg_of_le
      (fun j => inv_nonneg.mpr (Nat.cast_nonneg _)) (fun j => ?_) (hs.mul_left 18)
    have hb := nextPrimeCertificate_le_eighteen_mul (j + 1) (by omega)
    have hc : 0 < nextPrimeCertificate (j + 1) :=
      zero_lt_one.trans_le (nextPrimeCertificate_ge_one (j + 1) (by omega))
    have hn : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hi := (inv_le_inv₀ (mul_pos (by norm_num : (0 : ℝ) < 18) hn) hc).mpr hb
    rw [mul_inv_rev] at hi
    norm_num at hi
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp hshift)

theorem dense_nextPrimeCertificate_mass_tendsto :
    Tendsto (fun m : ℕ => ∑ j ∈ Finset.range m, (nextPrimeCertificate (j + 1))⁻¹)
      atTop atTop := by
  classical
  by_contra h
  apply dense_nextPrimeCertificate_reciprocal_not_summable
  exact (summable_iff_not_tendsto_nat_atTop_of_nonneg
    (fun j => inv_nonneg.mpr
      (zero_le_one.trans (nextPrimeCertificate_ge_one (j + 1) (by omega))))).mpr h

/-- The dense-head route has only one remaining asymptotic arithmetic input:
a vanishing upper budget for the actual normalized signed correlations. -/
theorem riemannHypothesis_of_denseNextPrime_signed_correlation_budget
    (b : ℕ → ℝ)
    (hcross : ∀ᶠ m in atTop,
      reciprocalEnergyCross (fun j => paretoNextPrimeHead (j + 1) - hilbertOne)
        (fun j => nextPrimeCertificate (j + 1)) m ≤ b m)
    (hbudget : Tendsto b atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_nextPrime_signed_correlation_budget (fun j => j + 1)
    (fun _ _ h => Nat.add_le_add_right h 1) (fun j => Nat.succ_pos j)
    b hcross hbudget dense_nextPrimeCertificate_mass_tendsto

end RiemannResearch.RH.QPrimeBalancedExactHead
