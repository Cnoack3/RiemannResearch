/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoPrimeNormalizedCancellation
import RiemannResearch.RH.ParetoCoprimeModulusRefinement
import RiemannResearch.LinearAlgebra.OrthogonalFarSupportBound

/-!
# Factorial refinement and the remaining prime cancellation channel

Source: continuation of the user-provided
`ParetoCapacityFormalization20260921_Continued(1).md` (2026-09-21).

The next factorial coprime certificate differs from the previous one by an
actual Hilbert vector invisible to every old observation. At a fresh prime
its pairing with the new Schur innovation is exactly the positive source
`delta`. The old feasible error is orthogonal to this refinement vector.

Two-vector Bessel therefore yields a strictly sharper cancellation budget
than one-vector Cauchy--Schwarz. The estimate is unconditional, but it is
sharp abstractly and does not by itself exclude `kappa` near `-delta`.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

open RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteHilbertGram

def factorialPrimeRefinement (n : ℕ) : ThresholdHilbert :=
  infiniteCoprimeCertificate (n + 3).factorial -
    infiniteCoprimeCertificate (n + 2).factorial

theorem tailInnovation_inner_of_old_observation_zero
    (n : ℕ) (z : ThresholdHilbert)
    (hz : ∀ i : Fin n, inner ℝ (tailAtom i.val) z = 0) :
    inner ℝ (tailInnovation n) z = inner ℝ (tailAtom n) z := by
  rw [tailInnovation, screened, inner_sub_left, inner_synthesis_left]
  simp only [hz, mul_zero, Finset.sum_const_zero, sub_zero]

theorem factorialPrimeRefinement_old_observation_zero
    (n : ℕ) (i : Fin (n + 1)) :
    inner ℝ (tailAtom i.val) (factorialPrimeRefinement n) = 0 := by
  simpa only [factorialPrimeRefinement] using
    (infiniteCoprimeCertificate_refinement_observation_zero (n + 1)
      (Nat.factorial_ne_zero (n + 2))
      (Nat.dvd_factorial (by decide) (by omega))
      (Nat.factorial_ne_zero (n + 3))
      (Nat.factorial_dvd_factorial (by omega))
      (fun j => Nat.dvd_factorial (by omega) (by omega)) i)

theorem tailAtom_inner_factorialPrimeRefinement
    (n : ℕ) (hp : Nat.Prime (n + 3)) :
    inner ℝ (tailAtom (n + 1)) (factorialPrimeRefinement n) =
      factorialPrimeDelta n := by
  have hQ := infiniteCoprimeCertificate_observation (n + 2) (n + 3).factorial
    (Nat.factorial_ne_zero _)
    (Nat.dvd_factorial (by decide) (by omega))
    (fun i => Nat.dvd_factorial (by omega) (by omega))
    (Fin.last (n + 1))
  have hP := infiniteCoprimeCertificate_fresh_prime_observation
    (n + 2).factorial (n + 1)
    (Nat.factorial_ne_zero _)
    (Nat.dvd_factorial (by decide) (by omega))
    (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hp)
    (by simpa only [hp.dvd_factorial] using (by omega : ¬ n + 3 ≤ n + 2))
  simp only [Fin.val_last, reciprocalSource, Nat.add_assoc, Nat.reduceAdd] at hQ hP
  simp only [factorialPrimeRefinement, factorialPrimeDelta, inner_sub_right, hQ, hP]
  ring

theorem tailInnovation_inner_factorialPrimeRefinement
    (n : ℕ) (hp : Nat.Prime (n + 3)) :
    inner ℝ (tailInnovation (n + 1)) (factorialPrimeRefinement n) =
      factorialPrimeDelta n := by
  rw [tailInnovation_inner_of_old_observation_zero (n + 1)
    (factorialPrimeRefinement n) (factorialPrimeRefinement_old_observation_zero n)]
  exact tailAtom_inner_factorialPrimeRefinement n hp

theorem factorialPrimeError_refinement_orthogonal (n : ℕ) :
    inner ℝ
      (infiniteCoprimeCertificate (n + 2).factorial - tailMinimum (n + 1))
      (factorialPrimeRefinement n) = 0 := by
  have hgap := infiniteCoprimeCertificate_refinement_gap (n + 1)
    (Nat.factorial_ne_zero (n + 2))
    (Nat.dvd_factorial (by decide) (by omega))
    (Nat.factorial_ne_zero (n + 3))
    (Nat.factorial_dvd_factorial (by omega))
    (fun i => Nat.dvd_factorial (by omega) (by omega))
  change ‖infiniteCoprimeCertificate (n + 3).factorial - tailMinimum (n + 1)‖ ^ 2 =
      ‖infiniteCoprimeCertificate (n + 2).factorial - tailMinimum (n + 1)‖ ^ 2 +
        ‖factorialPrimeRefinement n‖ ^ 2 at hgap
  have hdecomp :
      infiniteCoprimeCertificate (n + 3).factorial - tailMinimum (n + 1) =
        (infiniteCoprimeCertificate (n + 2).factorial - tailMinimum (n + 1)) +
          factorialPrimeRefinement n := by
    unfold factorialPrimeRefinement
    calc
      infiniteCoprimeCertificate (n + 3).factorial - tailMinimum (n + 1) =
          (infiniteCoprimeCertificate (n + 3).factorial -
            infiniteCoprimeCertificate (n + 2).factorial) +
          (infiniteCoprimeCertificate (n + 2).factorial - tailMinimum (n + 1)) :=
            (sub_add_sub_cancel _ _ _).symm
      _ = _ := add_comm _ _
  rw [hdecomp, norm_add_sq_real] at hgap
  linarith

/-- The refinement direction consumes a fixed positive part of the innovation
budget before the signed old-certificate error can contribute. -/
theorem factorialPrime_two_vector_cancellation_bound
    (n : ℕ) (hp : Nat.Prime (n + 3)) :
    (factorialPrimeError n) ^ 2 * ‖factorialPrimeRefinement n‖ ^ 2 +
        (factorialPrimeDelta n) ^ 2 *
          ‖infiniteCoprimeCertificate (n + 2).factorial - tailMinimum (n + 1)‖ ^ 2 ≤
      schurSigma (n + 1) *
        ‖infiniteCoprimeCertificate (n + 2).factorial - tailMinimum (n + 1)‖ ^ 2 *
        ‖factorialPrimeRefinement n‖ ^ 2 := by
  have h := RiemannResearch.LinearAlgebra.two_orthogonal_pairings_sq_le
    (tailInnovation (n + 1))
    (infiniteCoprimeCertificate (n + 2).factorial - tailMinimum (n + 1))
    (factorialPrimeRefinement n)
    (factorialPrimeError_refinement_orthogonal n)
  simpa only [factorialPrimeError, tailInnovation_inner_factorialPrimeRefinement n hp,
    schurSigma] using h

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
