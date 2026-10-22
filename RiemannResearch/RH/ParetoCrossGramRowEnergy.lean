/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoPrimeCrossStageCancellation
import RiemannResearch.Analysis.OrthogonalPairingEnergy

/-!
# Full factorial cross-Gram row energy

Source: continuation of the user-provided Pareto capacity handoff
(2026-09-21). Every signed entry of each finite row is retained.
Bessel controls the fixed base vector and each fixed column. The all-stage
row energy is summable exactly when the complete Schur gain series is.
Its nonsummability remains an open arithmetic premise sufficient for RH.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Analysis.OrthogonalPairingEnergy

/-- Signed finite row sum, including the diagonal, at every stage. -/
def factorialCrossGramRow (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), factorialPrimeCrossGram n j

def factorialCrossGramRowEnergy (n : ℕ) : ℝ :=
  (factorialCrossGramRow n)^2 / schurSigma (n+1)

theorem tailInnovation_fixed_pairing_energy_summable (x : ThresholdHilbert) :
    Summable (fun n => (inner ℝ (tailInnovation n) x)^2 / schurSigma n) :=
  pairing_energy_summable tailInnovation tailInnovation_pairwise_orthogonal
    tailInnovation_ne_zero x

theorem tailInnovation_fixed_pairing_energy_tsum_le (x : ThresholdHilbert) :
    (∑' n, (inner ℝ (tailInnovation n) x)^2 / schurSigma n) ≤ ‖x‖^2 :=
  pairing_energy_tsum_le tailInnovation tailInnovation_pairwise_orthogonal
    tailInnovation_ne_zero x

theorem factorialPrimeCrossGram_column_energy_summable (m : ℕ) :
    Summable (fun n => (factorialPrimeCrossGram n m)^2 / schurSigma (n+1)) := by
  exact (summable_nat_add_iff 1).mpr
    (tailInnovation_fixed_pairing_energy_summable (factorialPrimeRefinement m))

theorem factorialCrossGramRowEnergy_nonneg (n : ℕ) :
    0 ≤ factorialCrossGramRowEnergy n :=
  div_nonneg (sq_nonneg _) (schurSigma_pos _).le

/-- Exact finite-stage expression, with no primality hypothesis. -/
theorem schurGain_eq_factorialCrossGramRow (n : ℕ) :
    (schurEta (n+1))^2 / schurSigma (n+1) =
      (factorialCrossGramRow n +
        inner ℝ (tailInnovation (n+1)) (infiniteCoprimeCertificate (Nat.factorial 2)))^2 /
      schurSigma (n+1) := by
  rw [schurEta_eq_base_add_crossGram]
  unfold factorialCrossGramRow
  rw [add_comm]


/-- Exact capacity telescope over every stage, retaining the base cross term. -/
theorem tailCapacity_eq_factorialCrossGramRow_sum (N : ℕ) :
    tailCapacity (N+1) = tailCapacity 1 +
      ∑ n ∈ Finset.range N,
        (factorialCrossGramRow n +
          inner ℝ (tailInnovation (n+1)) (infiniteCoprimeCertificate (Nat.factorial 2)))^2 /
        schurSigma (n+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [capacity_schur_step (N+1), ih, Finset.sum_range_succ,
      schurGain_eq_factorialCrossGramRow]
    ring

/-- Removing the fixed base pairing does not change summability. -/
theorem factorialCrossGramRowEnergy_summable_iff_schurGain :
    Summable factorialCrossGramRowEnergy ↔
      Summable (fun n => (schurEta n)^2 / schurSigma n) := by
  have hb := (summable_nat_add_iff 1).mpr
    (tailInnovation_fixed_pairing_energy_summable
      (infiniteCoprimeCertificate (Nat.factorial 2)))
  have h := weighted_square_add_summable_iff factorialCrossGramRow
    (fun n => inner ℝ (tailInnovation (n+1)) (infiniteCoprimeCertificate (Nat.factorial 2)))
    (fun n => schurSigma (n+1)) (fun n => (schurSigma_pos _).le) hb
  have he : (fun n => (factorialCrossGramRow n +
        inner ℝ (tailInnovation (n+1)) (infiniteCoprimeCertificate (Nat.factorial 2)))^2 /
      schurSigma (n+1)) =
      (fun n => (schurEta (n+1))^2 / schurSigma (n+1)) := by
    funext n
    exact (schurGain_eq_factorialCrossGramRow n).symm
  rw [he] at h
  change Summable (fun n => (schurEta (n+1))^2 / schurSigma (n+1)) ↔
    Summable factorialCrossGramRowEnergy at h
  have hshift : Summable (fun n => (schurEta (n+1))^2 / schurSigma (n+1)) ↔
      Summable (fun n => (schurEta n)^2 / schurSigma n) :=
    summable_nat_add_iff (f := fun n : ℕ => (schurEta n)^2 / schurSigma n) 1
  exact h.symm.trans hshift

/-- No RH-to-density provider is needed for this necessary condition. -/
theorem factorialCrossGramRowEnergy_summable_of_not_RH
    (hRH : ¬ RiemannHypothesis) : Summable factorialCrossGramRowEnergy :=
  factorialCrossGramRowEnergy_summable_iff_schurGain.mpr
    (schurGain_summable_of_not_RH hRH)

/-- CONDITIONAL RESEARCH REDUCTION: the actual signed row-energy
nonsummability premise remains Open. -/
theorem riemannHypothesis_of_factorialCrossGramRowEnergy_not_summable
    (h : ¬ Summable factorialCrossGramRowEnergy) : RiemannHypothesis := by
  by_contra hRH
  exact h (factorialCrossGramRowEnergy_summable_of_not_RH hRH)

/-- Nonnegative partial-sum divergence is the same open arithmetic target. -/
theorem factorialCrossGramRowEnergy_not_summable_iff :
    ¬ Summable factorialCrossGramRowEnergy ↔
      Tendsto (fun N => ∑ n ∈ Finset.range N, factorialCrossGramRowEnergy n)
        atTop atTop :=
  not_summable_iff_tendsto_nat_atTop_of_nonneg factorialCrossGramRowEnergy_nonneg

/-- Any fixed finite signed combination of columns has finite energy. -/
theorem factorialPrimeCrossGram_finite_columns_energy_summable
    (s : Finset ℕ) (a : ℕ → ℝ) :
    Summable (fun n =>
      (∑ m ∈ s, a m * factorialPrimeCrossGram n m)^2 / schurSigma (n+1)) := by
  have h := (summable_nat_add_iff 1).mpr
    (tailInnovation_fixed_pairing_energy_summable
      (∑ m ∈ s, a m • factorialPrimeRefinement m))
  simpa only [inner_sum, inner_smul_right, factorialPrimeCrossGram] using h

/-- Deleting or modifying finitely many fixed columns cannot alter the
signed row-energy summability target. Coefficients do not depend on n. -/
theorem factorialCrossGramRowEnergy_finite_columns_iff
    (s : Finset ℕ) (a : ℕ → ℝ) :
    Summable (fun n =>
      (factorialCrossGramRow n - ∑ m ∈ s, a m * factorialPrimeCrossGram n m)^2 /
        schurSigma (n+1)) ↔ Summable factorialCrossGramRowEnergy := by
  have hb : Summable (fun n =>
      (-(∑ m ∈ s, a m * factorialPrimeCrossGram n m))^2 / schurSigma (n+1)) := by
    simpa only [neg_sq] using
      factorialPrimeCrossGram_finite_columns_energy_summable s a
  change Summable (fun n =>
      (factorialCrossGramRow n - ∑ m ∈ s, a m * factorialPrimeCrossGram n m)^2 /
        schurSigma (n+1)) ↔
    Summable (fun n => (factorialCrossGramRow n)^2 / schurSigma (n+1))
  simpa only [sub_eq_add_neg] using
    (weighted_square_add_summable_iff factorialCrossGramRow
      (fun n => -(∑ m ∈ s, a m * factorialPrimeCrossGram n m))
      (fun n => schurSigma (n+1)) (fun n => (schurSigma_pos _).le) hb)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
