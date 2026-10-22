/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoPrimePivotCertificates
import RiemannResearch.RH.ParetoMovingRemainderTransfer
import RiemannResearch.RH.ParetoCoprimeDefectScreening
import Mathlib.Analysis.PSeries

/-!
# Unconditional summability of raw prime-charge comparison models

Source: the exact signed raw decomposition in ParetoCoprimeDefectScreening,
the finite-support pivot bounds in ParetoPrimePivotCertificates, and standard
p-series and Bessel estimates. This rules out the specified raw family as a
divergent provider for ParetoMovingRemainderTransfer; it does not prove RH.

The weight is the complete prime Schur inverse, with all historical rows.
Raw charges Q/p^2 and a fixed Hilbert-vector pairing have finite weighted
energy unconditionally. Their source-balanced dyadic amplitudes have
summable squares for arbitrary block tests. The complete discrepancy to the
actual moving amplitude is square summable if and only if that actual
amplitude is square summable. Exact mixed and source-shift identities precede
the estimates; zero energy denominators use the existing total definitions.
-/


noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Analysis.WeightedScalarEnergy
open RiemannResearch.Analysis.DyadicWeightedContrast


def primeRawCharge (Q : ℝ) (n : ℕ) : ℝ :=
  Q / ((n+3 : ℕ) : ℝ)^2


theorem primeSchurWeight_rawCharge_le (Q : ℝ) (n : ℕ) :
    primeSchurWeight n * (primeRawCharge Q n)^2 ≤
      10 * Q^2 / ((n+3 : ℕ) : ℝ)^2 := by
  by_cases hp : Nat.Prime (n+3)
  · have h := prime_schur_inverse_le_ten_sq n hp
    simp only [primeSchurWeight, if_pos hp, primeRawCharge]
    calc
      _ = (Q / ((n+3 : ℕ) : ℝ)^2)^2 * (1 / schurSigma (n+1)) := by ring
      _ ≤ (Q / ((n+3 : ℕ) : ℝ)^2)^2 * (10 * ((n+3 : ℕ) : ℝ)^2) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = _ := by field_simp
  · simp [primeSchurWeight,hp]
    positivity


theorem primeRawCharge_energy_summable (Q : ℝ) :
    Summable (fun n => primeSchurWeight n * (primeRawCharge Q n)^2) := by
  have hs0 : Summable (fun n : ℕ => ((n : ℝ)^2)⁻¹) := by
    simpa only [Real.rpow_two] using
      (Real.summable_nat_rpow_inv (p := 2)).2 (by norm_num)
  have hs : Summable (fun n : ℕ => 1 / ((n+3 : ℕ) : ℝ)^2) := by
    simpa only [one_div] using (summable_nat_add_iff 3).mpr hs0
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (primeSchurWeight_nonneg n) (sq_nonneg _))
    (primeSchurWeight_rawCharge_le Q)
  simpa only [mul_one_div] using hs.mul_left (10 * Q^2)


def primeRawModelRow (Q : ℝ) (z : ThresholdHilbert) (n : ℕ) : ℝ :=
  primeRawCharge Q n + inner ℝ (tailInnovation (n+1)) z


theorem primeRawModelRow_energy_split (Q : ℝ) (z : ThresholdHilbert) (n : ℕ) :
    primeSchurWeight n * (primeRawModelRow Q z n)^2 =
      primeSchurWeight n * (primeRawCharge Q n)^2 +
      2 * primeSchurWeight n * primeRawCharge Q n *
        inner ℝ (tailInnovation (n+1)) z +
      primeSchurWeight n * (inner ℝ (tailInnovation (n+1)) z)^2 := by
  unfold primeRawModelRow
  ring


theorem primeRawModelRow_energy_summable (Q : ℝ) (z : ThresholdHilbert) :
    Summable (fun n => primeSchurWeight n * (primeRawModelRow Q z n)^2) := by
  have hz : Summable (fun n =>
      (inner ℝ (tailInnovation (n+1)) z)^2 / schurSigma (n+1)) :=
    (summable_nat_add_iff 1).mpr (tailInnovation_fixed_pairing_energy_summable z)
  have hb : Summable (fun n =>
      primeSchurWeight n * (inner ℝ (tailInnovation (n+1)) z)^2) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (primeSchurWeight_nonneg n) (sq_nonneg _)) _ hz
    intro n
    by_cases hp : Nat.Prime (n+3)
    · simp [primeSchurWeight,hp,div_eq_mul_inv,mul_comm]
    · simp only [primeSchurWeight,if_neg hp,zero_mul]
      exact div_nonneg (sq_nonneg _) (schurSigma_pos _).le
  have he : Summable (fun n => primeSchurWeight n *
      (primeRawCharge Q n - primeRawModelRow Q z n)^2) := by
    simpa only [primeRawModelRow, sub_add_cancel_left, neg_sq] using hb
  exact model_square_summable primeSchurWeight (primeRawCharge Q)
    (primeRawModelRow Q z) primeSchurWeight_nonneg (primeRawCharge_energy_summable Q) he


def primeRawModelPairing (N k : ℕ) (f : ℕ → ℝ) (Q : ℝ)
    (z : ThresholdHilbert) : ℝ :=
  product (Finset.range k) (fun i => primeSchurWeight (N+i))
    (primeBlockBalancedTest N k f) (fun i => primeRawModelRow Q z (N+i))



theorem primeRawModelPairing_source_shift (N k : ℕ) (f : ℕ → ℝ)
    (Q : ℝ) (z : ThresholdHilbert) :
    product (Finset.range k) (fun i => primeSchurWeight (N+i))
      (primeBlockBalancedTest N k f)
      (fun i => primeRawModelRow Q z (N+i) - factorialPrimeDelta (N+i)) =
        primeRawModelPairing N k f Q z := by
  have hz : product (Finset.range k) (fun i => primeSchurWeight (N+i))
      (primeBlockBalancedTest N k f) (fun i => factorialPrimeDelta (N+i)) = 0 := by
    simpa only [product,mul_comm,mul_left_comm,mul_assoc] using
      primeBlockBalancedTest_source_zero N k f
  calc
    _ = primeRawModelPairing N k f Q z -
        product (Finset.range k) (fun i => primeSchurWeight (N+i))
          (primeBlockBalancedTest N k f) (fun i => factorialPrimeDelta (N+i)) := by
      simp only [primeRawModelPairing, product, mul_sub, Finset.sum_sub_distrib]
    _ = _ := by rw [hz,sub_zero]


def primeRawModelCertificate (N k : ℕ) (f : ℕ → ℝ) (Q : ℝ)
    (z : ThresholdHilbert) : ℝ :=
  (primeRawModelPairing N k f Q z)^2 / primeBlockContrastEnergy N k f


theorem primeRawModelCertificate_dyadic_summable (f : ℕ → ℕ → ℝ)
    (Q : ℝ) (z : ThresholdHilbert) :
    Summable (fun j => primeRawModelCertificate (2^j) (2^j) (f j) Q z) := by
  exact dyadic_pairing_energy_summable primeSchurWeight (primeRawModelRow Q z)
    (fun j => primeBlockBalancedTest (2^j) (2^j) (f j))
    primeSchurWeight_nonneg (primeRawModelRow_energy_summable Q z)


def primeRawModelAmplitude (j : ℕ) (f : ℕ → ℕ → ℝ) (Q : ℝ)
    (z : ThresholdHilbert) : ℝ :=
  primeRawModelPairing (2^j) (2^j) (f j) Q z /
    Real.sqrt (primeBlockContrastEnergy (2^j) (2^j) (f j))


theorem primeRawModelAmplitude_sq (j : ℕ) (f : ℕ → ℕ → ℝ)
    (Q : ℝ) (z : ThresholdHilbert) :
    (primeRawModelAmplitude j f Q z)^2 =
      primeRawModelCertificate (2^j) (2^j) (f j) Q z := by
  unfold primeRawModelAmplitude primeRawModelCertificate
  rw [div_pow, Real.sq_sqrt]
  exact square_nonneg _ _ _ (fun i _ => primeSchurWeight_nonneg (2^j+i))


theorem primeRawModelAmplitude_square_summable (f : ℕ → ℕ → ℝ)
    (Q : ℝ) (z : ThresholdHilbert) :
    Summable (fun j => (primeRawModelAmplitude j f Q z)^2) := by
  simpa only [primeRawModelAmplitude_sq] using
    primeRawModelCertificate_dyadic_summable f Q z


theorem primeMovingCRT_rawModel_error_summable_iff (f : ℕ → ℕ → ℝ)
    (Q : ℝ) (z : ThresholdHilbert) :
    Summable (fun j =>
      (primeMovingCRTAmplitude j f - primeRawModelAmplitude j f Q z)^2) ↔
      Summable (fun j => (primeMovingCRTAmplitude j f)^2) := by
  have hm : Summable (fun j => (-(primeRawModelAmplitude j f Q z))^2 / (1 : ℝ)) := by
    simpa only [neg_sq,div_one] using primeRawModelAmplitude_square_summable f Q z
  simpa only [sub_eq_add_neg,div_one] using
    RiemannResearch.Analysis.OrthogonalPairingEnergy.weighted_square_add_summable_iff
      (fun j => primeMovingCRTAmplitude j f)
      (fun j => -(primeRawModelAmplitude j f Q z)) (fun _ => (1 : ℝ))
      (fun _ => by norm_num) hm


theorem coprimePrimeRawCharge_eq (n : ℕ) (hp : Nat.Prime (n+3)) :
    coprimeObservationDefect 2 (n+3) =
      primeRawCharge (1 + ‖infiniteCoprimeCertificate 2‖^2/2) n := by
  have hd : ¬ 2 ∣ n+3 := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h1 | h2 <;> omega
  simpa only [show n+1+2=n+3 by omega,hd,if_false,primeRawCharge] using
    coprimeObservationDefect_two (n+1)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
