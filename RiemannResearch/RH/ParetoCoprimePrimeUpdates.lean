/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoCoprimePrimeObservation
import RiemannResearch.RH.IntegerDPPSchur
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Prime corrections for a growing Pareto dictionary

Source: continuation of the user-provided Pareto capacity formalization
(2026-09-21). The fresh-prime arithmetic defect is combined with the
actual signed Schur numerator. Correcting that defect in the screened
new direction gives a feasible next-stage certificate and an exact
decrease of its squared-distance gap. The original certificate is
reset at each application; no iterated divergence estimate is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.RH.Pareto.IntegerDPP

theorem tailInnovation_inner_feasible_error (n : ℕ) (z : ThresholdHilbert)
    (hz : ∀ i : Fin n, inner ℝ (tailAtom i.val) z = reciprocalSource n i) :
    inner ℝ (tailInnovation n) (z - tailMinimum n) =
      inner ℝ (tailAtom n) (z - tailMinimum n) := by
  rw [tailInnovation, screened, inner_sub_left, inner_synthesis_left]
  simp only [inner_sub_right, hz, tailMinimum_observation, sub_self, mul_zero,
    Finset.sum_const_zero, sub_zero]

theorem schurEta_fresh_prime_decomposition (n P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P)
    (hq : Nat.Prime (n + 2)) (hqP : ¬ (n + 2) ∣ P) :
    schurEta n = coprimePrimeDefect P (n + 2) +
      inner ℝ (tailInnovation n) (infiniteCoprimeCertificate P - tailMinimum n) := by
  rw [tailInnovation_inner_feasible_error n (infiniteCoprimeCertificate P)
      (infiniteCoprimeCertificate_observation n P hP h2 hmod),
    inner_sub_right,
    infiniteCoprimeCertificate_fresh_prime_observation P n hP h2 hq hqP]
  unfold schurEta
  ring

theorem capacity_schur_fresh_prime (n P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P)
    (hq : Nat.Prime (n + 2)) (hqP : ¬ (n + 2) ∣ P) :
    tailCapacity (n + 1) - tailCapacity n =
      (coprimePrimeDefect P (n + 2) +
        inner ℝ (tailInnovation n) (infiniteCoprimeCertificate P - tailMinimum n)) ^ 2 /
      schurSigma n := by
  rw [capacity_schur_increment,
    schurEta_fresh_prime_decomposition n P hP h2 hmod hq hqP]


theorem tailInnovation_old_observation (n : ℕ) (i : Fin n) :
    inner ℝ (tailAtom i.val) (tailInnovation n) = 0 :=
  inner_old_screened (finiteTailAtom_independent n) (fun _ : Unit => tailAtom n) i ()

theorem tailInnovation_inner_minimum (n : ℕ) :
    inner ℝ (tailInnovation n) (tailMinimum n) = 0 := by
  rw [real_inner_comm, tailMinimum, minimumVector, inner_synthesis_left]
  simp only [tailInnovation_old_observation, mul_zero, Finset.sum_const_zero]

theorem tailInnovation_self_observation (n : ℕ) :
    inner ℝ (tailAtom n) (tailInnovation n) = schurSigma n := by
  have h := real_inner_self_eq_norm_sq (tailInnovation n)
  change inner ℝ
    (tailAtom n - Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (inverseCoeff (finiteTailAtom_independent n) (tailAtom n)))
    (tailInnovation n) = schurSigma n at h
  rw [inner_sub_left, inner_synthesis_left] at h
  simpa only [tailInnovation_old_observation, mul_zero, Finset.sum_const_zero,
    sub_zero] using h

theorem infiniteCoprimeCertificate_prime_innovation (n P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P)
    (hq : Nat.Prime (n + 2)) (hqP : ¬ (n + 2) ∣ P) :
    inner ℝ (tailInnovation n) (infiniteCoprimeCertificate P) =
      schurEta n - coprimePrimeDefect P (n + 2) := by
  have h := schurEta_fresh_prime_decomposition n P hP h2 hmod hq hqP
  rw [inner_sub_right, tailInnovation_inner_minimum, sub_zero] at h
  linarith

/-- Add exactly the missing prime observation in the screened new direction. -/
def primeCorrectedCoprimeCertificate (n P : ℕ) : ThresholdHilbert :=
  infiniteCoprimeCertificate P +
    (coprimePrimeDefect P (n + 2) / schurSigma n) • tailInnovation n

theorem primeCorrectedCoprimeCertificate_observation (n P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P)
    (hq : Nat.Prime (n + 2)) (hqP : ¬ (n + 2) ∣ P) (i : Fin (n + 1)) :
    inner ℝ (tailAtom i.val) (primeCorrectedCoprimeCertificate n P) =
      reciprocalSource (n + 1) i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.val_last, primeCorrectedCoprimeCertificate, inner_add_right,
      inner_smul_right, tailInnovation_self_observation,
      infiniteCoprimeCertificate_fresh_prime_observation P n hP h2 hq hqP,
      reciprocalSource]
    rw [div_mul_cancel₀ _ (ne_of_gt (schurSigma_pos n))]
    ring
  · simp only [Fin.val_castSucc, primeCorrectedCoprimeCertificate, inner_add_right,
      inner_smul_right, tailInnovation_old_observation, mul_zero, add_zero]
    exact infiniteCoprimeCertificate_observation n P hP h2 hmod j

/-- Full signed energy of the corrected certificate, including its cross term. -/
theorem primeCorrectedCoprimeCertificate_energy (n P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P)
    (hq : Nat.Prime (n + 2)) (hqP : ¬ (n + 2) ∣ P) :
    ‖primeCorrectedCoprimeCertificate n P‖ ^ 2 =
      ‖infiniteCoprimeCertificate P‖ ^ 2 +
        (2 * coprimePrimeDefect P (n + 2) * schurEta n -
          (coprimePrimeDefect P (n + 2)) ^ 2) / schurSigma n := by
  have hc : inner ℝ (infiniteCoprimeCertificate P) (tailInnovation n) =
      schurEta n - coprimePrimeDefect P (n + 2) := by
    rw [real_inner_comm]
    exact infiniteCoprimeCertificate_prime_innovation n P hP h2 hmod hq hqP
  rw [primeCorrectedCoprimeCertificate, norm_add_sq_real,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [inner_smul_right, hc]
  change _ + _ + _ * schurSigma n = _
  field_simp [ne_of_gt (schurSigma_pos n)]
  ring

/-- The growing-dictionary gap keeps the complete squared correction. -/
theorem primeCorrectedCoprimeCertificate_gap (n P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P)
    (hq : Nat.Prime (n + 2)) (hqP : ¬ (n + 2) ∣ P) :
    ‖primeCorrectedCoprimeCertificate n P - tailMinimum (n + 1)‖ ^ 2 =
      ‖infiniteCoprimeCertificate P - tailMinimum n‖ ^ 2 -
        (schurEta n - coprimePrimeDefect P (n + 2)) ^ 2 / schurSigma n := by
  have hold := finiteTailCertificate_energy_completion n (infiniteCoprimeCertificate P)
    (infiniteCoprimeCertificate_observation n P hP h2 hmod)
  have hnew := finiteTailCertificate_energy_completion (n + 1)
    (primeCorrectedCoprimeCertificate n P)
    (primeCorrectedCoprimeCertificate_observation n P hP h2 hmod hq hqP)
  rw [primeCorrectedCoprimeCertificate_energy n P hP h2 hmod hq hqP,
    capacity_schur_step] at hnew
  have hid :
      (2 * coprimePrimeDefect P (n + 2) * schurEta n -
        (coprimePrimeDefect P (n + 2)) ^ 2) / schurSigma n -
        (schurEta n) ^ 2 / schurSigma n =
      -(schurEta n - coprimePrimeDefect P (n + 2)) ^ 2 / schurSigma n := by ring
  rw [neg_div] at hid
  linarith

theorem primeCorrectedCoprimeCertificate_gap_le (n P : ℕ)
    (hP : P ≠ 0) (h2 : 2 ∣ P)
    (hmod : ∀ i : Fin n, i.val + 2 ∣ P)
    (hq : Nat.Prime (n + 2)) (hqP : ¬ (n + 2) ∣ P) :
    ‖primeCorrectedCoprimeCertificate n P - tailMinimum (n + 1)‖ ^ 2 ≤
      ‖infiniteCoprimeCertificate P - tailMinimum n‖ ^ 2 := by
  rw [primeCorrectedCoprimeCertificate_gap n P hP h2 hmod hq hqP]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (le_of_lt (schurSigma_pos n)))


/-- A concrete old dictionary: no unspecified common-modulus assumption remains. -/
theorem capacity_schur_factorial_fresh_prime (n : ℕ) (hn : 0 < n)
    (hq : Nat.Prime (n + 2)) :
    tailCapacity (n + 1) - tailCapacity n =
      (coprimePrimeDefect (n + 1).factorial (n + 2) +
        inner ℝ (tailInnovation n)
          (infiniteCoprimeCertificate (n + 1).factorial - tailMinimum n)) ^ 2 /
      schurSigma n := by
  apply capacity_schur_fresh_prime n (n + 1).factorial (Nat.factorial_ne_zero _)
  · exact Nat.dvd_factorial (by decide) (by omega)
  · intro i
    exact Nat.dvd_factorial (by omega) (by omega)
  · exact hq
  · rw [hq.dvd_factorial]
    omega

theorem primeCorrectedCoprimeCertificate_factorial_gap (n : ℕ) (hn : 0 < n)
    (hq : Nat.Prime (n + 2)) :
    ‖primeCorrectedCoprimeCertificate n (n + 1).factorial -
        tailMinimum (n + 1)‖ ^ 2 =
      ‖infiniteCoprimeCertificate (n + 1).factorial - tailMinimum n‖ ^ 2 -
        (schurEta n - coprimePrimeDefect (n + 1).factorial (n + 2)) ^ 2 /
          schurSigma n := by
  apply primeCorrectedCoprimeCertificate_gap n (n + 1).factorial
    (Nat.factorial_ne_zero _)
  · exact Nat.dvd_factorial (by decide) (by omega)
  · intro i
    exact Nat.dvd_factorial (by omega) (by omega)
  · exact hq
  · rw [hq.dvd_factorial]
    omega


end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
