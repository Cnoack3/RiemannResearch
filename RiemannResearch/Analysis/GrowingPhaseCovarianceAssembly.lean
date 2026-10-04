import RiemannResearch.Analysis.PrimePowerCovarianceConjugation
import Mathlib.Tactic.Ring

/-!
# Conditional assembly of the full integer-frequency Gram estimate

Source: user-provided manuscript `Prime_Phases_Agenda_Proof_Attempts.tex`,
Theorem `growing-phase-gram`.

The full signed prime-power covariance kernel and its arithmetic bound are
proved by the imported modules. This module is a deterministic consumer of
an explicit entrywise error estimate. It does not supply the actual-zeta
Landau/FMZ estimate and does not assert zero-phase conditioning.
-/

open scoped BigOperators NNReal

namespace RiemannResearch.Fourier

/-- The exact signed covariance on every positive integer frequency. -/
noncomputable def primePowerCovarianceSignedEntry (n m : ℕ) : ℂ :=
  ((-1 / (2 * Real.pi) : ℝ) : ℂ) *
    (primePowerCovarianceSymmetricEntry n m : ℂ)

private theorem pairing_add_kernel {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (R S : ι → ι → ℂ) :
    finiteGramErrorPairing s a (fun n m => R n m + S n m) =
      finiteGramErrorPairing s a R + finiteGramErrorPairing s a S := by
  unfold finiteGramErrorPairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

private theorem pairing_mul_kernel {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (R : ι → ι → ℂ) (c : ℂ) :
    finiteGramErrorPairing s a (fun n m => c * R n m) =
      c * finiteGramErrorPairing s a R := by
  unfold finiteGramErrorPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Once a uniform entrywise provider is supplied, the full Gram error has
    precisely the cardinality loss for its remainder and the explicit
    logarithmic arithmetic covariance budget. Composite frequencies remain
    in the dictionary. The analytic provider is the hypothesis `hentry`. -/
theorem fullIntegerGramErrorPairing_bound_of_entrywise_remainder
    (N : ℕ) (a : ℕ → ℂ) (G : ℕ → ℕ → ℂ) (t : ℝ) (η : ℝ≥0)
    (hentry : ∀ n ∈ Finset.Ioc 0 N, ∀ m ∈ Finset.Ioc 0 N,
      ‖G n m - (if n = m then (1 : ℂ) else 0) -
        (t : ℂ) * primePowerCovarianceSignedEntry n m‖ ≤ (η : ℝ)) :
    ‖finiteGramErrorPairing (Finset.Ioc 0 N) a
      (fun n m => G n m - (if n = m then (1 : ℂ) else 0))‖ ≤
      ((N : ℝ) * η + |t| * ((Real.log N + Real.log 4 + 4) / (2 * Real.pi))) *
        (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2) := by
  let R : ℕ → ℕ → ℂ := fun n m =>
    G n m - (if n = m then (1 : ℂ) else 0) -
      (t : ℂ) * primePowerCovarianceSignedEntry n m
  have herror := finiteGramErrorPairing_norm_le_card_l2 (Finset.Ioc 0 N) a R
    (η : ℝ) η.property hentry
  simp only [Nat.card_Ioc, Nat.sub_zero] at herror
  have hmain :
      ‖finiteGramErrorPairing (Finset.Ioc 0 N) a primePowerCovarianceSignedEntry‖ ≤
        ((Real.log N + Real.log 4 + 4) / (2 * Real.pi)) *
          (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2) :=
    primePowerCovariance_normalized_pairing_bound N a
  have hkernel :
      (fun n m => G n m - (if n = m then (1 : ℂ) else 0)) =
        (fun n m => R n m + (t : ℂ) * primePowerCovarianceSignedEntry n m) := by
    funext n m
    dsimp [R]
    ring
  rw [hkernel, pairing_add_kernel, pairing_mul_kernel]
  calc
    _ ≤ ‖finiteGramErrorPairing (Finset.Ioc 0 N) a R‖ +
        ‖(t : ℂ) * finiteGramErrorPairing (Finset.Ioc 0 N) a
          primePowerCovarianceSignedEntry‖ := norm_add_le _ _
    _ = ‖finiteGramErrorPairing (Finset.Ioc 0 N) a R‖ +
        |t| * ‖finiteGramErrorPairing (Finset.Ioc 0 N) a
          primePowerCovarianceSignedEntry‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (η : ℝ) * (N : ℝ) * (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2) +
        |t| * (((Real.log N + Real.log 4 + 4) / (2 * Real.pi)) *
          (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2)) :=
      add_le_add herror (mul_le_mul_of_nonneg_left hmain (abs_nonneg t))
    _ = _ := by ring

end RiemannResearch.Fourier
