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

end RiemannResearch.RH.QDivisorHilbert
