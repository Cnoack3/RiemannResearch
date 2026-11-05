/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisorWaveletDensity
import RiemannResearch.RH.QDivisorWaveletFactorization
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QDivisibilityResidueCoefficients
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact divisor-basis dilation coefficients and signed finite errors

Source: user-provided coprime-conductor research request, 22 October 2026,
following commit f8284c0d39e8ae1817bd24297da9a24f984c23bc.
The statement and proof strategy are the finite Moebius expansion followed
by the existing complete-Q dilation identity. The squared divisor scale
cancels exactly. The finite error decomposition retains its entire remainder.

RH consumer: target and legal residue coefficients can be compared in the
same ambient basis without deleting signed discrepancies or physical tails.
Ambient orthogonality supplies no legal-preservation hypothesis.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.QDivisorHilbert
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity

/-- Finite signed divisor formula with the complete dilated physical means. -/
theorem normalizedDivisorWavelet_inner_dilation (f : QHilbert) (t : ℕ+) :
    inner ℝ f (normalizedDivisorWavelet t) =
      (∑ d ∈ (t : ℕ).divisors, (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) *
        inversePowerMean 0 (fun n => qSequence f (d * n))) /
        Real.sqrt (qJordanTwo (t : ℕ)) := by
  unfold normalizedDivisorWavelet divisorWavelet
  rw [real_inner_smul_right, inner_sum]
  have he : (∑ d ∈ (t : ℕ).divisors,
      ((ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) * (d : ℝ) ^ 2) *
        inner ℝ f (qDivisor d)) =
      ∑ d ∈ (t : ℕ).divisors, (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) *
        inversePowerMean 0 (fun n => qSequence f (d * n)) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))
    rw [inner_qDivisor_eq_dilation f d (Nat.pos_of_mem_divisors hd)]
    field_simp
  simp_rw [real_inner_smul_right]
  rw [he]
  ring

/-- Legal atom columns in the ambient basis, with every signed divisor term retained. -/
theorem normalizedDivisorWavelet_residue_coefficient (d : ℕ) (t : ℕ+) :
    inner ℝ (qResidue d) (normalizedDivisorWavelet t) =
      qResidueDivisorCoefficient d (t : ℕ) / Real.sqrt (qJordanTwo (t : ℕ)) := by
  simpa only [qSequence_qResidue, qTwistedResidueMean, qResidueDivisorCoefficient] using
    normalizedDivisorWavelet_inner_dilation (qResidue d) t

/-- Exact selected-mode discrepancies plus the complete orthogonal remainder. -/
theorem divisorBasis_error_finite_exact (f g : QHilbert) (S : Finset ℕ+) :
    ‖f - g‖ ^ 2 =
      (∑ t ∈ S, (inner ℝ f (normalizedDivisorWavelet t) -
        inner ℝ g (normalizedDivisorWavelet t)) ^ 2) +
      ‖f - g - ∑ t ∈ S, (inner ℝ f (normalizedDivisorWavelet t) -
        inner ℝ g (normalizedDivisorWavelet t)) • normalizedDivisorWavelet t‖ ^ 2 := by
  let a := fun t : ℕ+ => inner ℝ (f - g) (normalizedDivisorWavelet t)
  have hn : ‖∑ t ∈ S, a t • normalizedDivisorWavelet t‖ ^ 2 =
      ∑ t ∈ S, (a t) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, normalizedDivisorWavelet_orthonormal.inner_sum]
    simp [pow_two]
  have hi : inner ℝ (f - g) (∑ t ∈ S, a t • normalizedDivisorWavelet t) =
      ∑ t ∈ S, (a t) ^ 2 := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [real_inner_smul_right]
    change a t * a t = (a t) ^ 2
    ring
  have he : ‖f - g‖ ^ 2 = (∑ t ∈ S, (a t) ^ 2) +
      ‖f - g - ∑ t ∈ S, a t • normalizedDivisorWavelet t‖ ^ 2 := by
    rw [norm_sub_sq_real (f - g), hn, hi]
    ring
  simpa only [a, inner_sub_left] using he

theorem divisorBasis_error_finite_lower (f g : QHilbert) (S : Finset ℕ+) :
    (∑ t ∈ S, (inner ℝ f (normalizedDivisorWavelet t) -
      inner ℝ g (normalizedDivisorWavelet t)) ^ 2) ≤ ‖f - g‖ ^ 2 := by
  rw [divisorBasis_error_finite_exact f g S]
  exact le_add_of_nonneg_right (sq_nonneg _)


/-- Finite Mobius inversion of divisibility indicators in the actual Q Hilbert space.
Source: user-requested exact expectation calculation; the scalar provider is
sum_divisorWaveletAF. No limiting interchange or RH hypothesis is used. -/
theorem sum_divisorWavelet (a : ℕ) :
    (∑ t ∈ a.divisors, divisorWavelet t) = (a : ℝ) ^ 2 • qDivisor a := by
  apply qSequence_injective
  funext n
  cases n with
  | zero => simp
  | succ n =>
    change qSequenceLinear (∑ t ∈ a.divisors, divisorWavelet t) (n + 1) =
      qSequenceLinear ((a : ℝ) ^ 2 • qDivisor a) (n + 1)
    rw [map_sum, map_smul]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ t ∈ a.divisors, qSequence (divisorWavelet t) (n + 1)) =
      (a : ℝ) ^ 2 * qSequence (qDivisor a) (n + 1)
    simp_rw [qSequence_divisorWavelet_succ, qSequence_qDivisor]
    simpa [divisorWaveletAF_apply, scaledDivisorAF, positiveDivisor] using
      sum_divisorWaveletAF a (n + 1)

/-- The complete dilated expectation is a finite sum of divisor-basis coordinates. -/
theorem dilation_mean_eq_sum_divisor_coefficients (f : QHilbert) (a : ℕ)
    (ha : 0 < a) :
    inversePowerMean 0 (fun n => qSequence f (a * n)) =
      ∑ t ∈ a.divisors, inner ℝ f (divisorWavelet t) := by
  have h := congrArg (fun g : QHilbert => inner ℝ f g) (sum_divisorWavelet a)
  rw [inner_sum, inner_smul_right, inner_qDivisor_eq_dilation f a ha] at h
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  field_simp at h
  nlinarith [sq_pos_of_ne_zero ha0]

/-- Exact expectation of every dilated normalized tensor/divisor wavelet. -/
theorem normalizedDivisorWavelet_dilation_mean (a : ℕ) (ha : 0 < a) (t : ℕ+) :
    inversePowerMean 0 (fun n => qSequence (normalizedDivisorWavelet t) (a * n)) =
      if (t : ℕ) ∣ a then Real.sqrt (qJordanTwo (t : ℕ)) else 0 := by
  rw [dilation_mean_eq_sum_divisor_coefficients _ a ha]
  have hi (b : ℕ) (hb : b ∈ a.divisors) :
      inner ℝ (normalizedDivisorWavelet t) (divisorWavelet b) =
        if b = (t : ℕ) then Real.sqrt (qJordanTwo (t : ℕ)) else 0 := by
    have hp := Nat.pos_of_mem_divisors hb
    have heq : divisorWavelet b =
        Real.sqrt (qJordanTwo b) • normalizedDivisorWavelet (⟨b, hp⟩ : ℕ+) :=
      divisorWavelet_eq_normalized_smul (⟨b, hp⟩ : ℕ+)
    rw [heq, inner_smul_right]
    rw [(orthonormal_iff_ite.mp normalizedDivisorWavelet_orthonormal) t ⟨b, hp⟩]
    by_cases he : b = (t : ℕ)
    · subst b
      have ht : t = (⟨(t : ℕ), hp⟩ : ℕ+) := Subtype.ext rfl
      simp only [if_pos ht, ite_true, mul_one]
    · have hne : t ≠ (⟨b, hp⟩ : ℕ+) := by
        intro h
        exact he (congrArg (fun x : ℕ+ => (x : ℕ)) h).symm
      simp [hne, he]
  simp_rw [Finset.sum_congr rfl hi]
  simp [Nat.mem_divisors, Nat.ne_of_gt ha]

#print axioms sum_divisorWavelet
#print axioms dilation_mean_eq_sum_divisor_coefficients
#print axioms normalizedDivisorWavelet_dilation_mean

end RiemannResearch.RH.QDivisorHilbert
