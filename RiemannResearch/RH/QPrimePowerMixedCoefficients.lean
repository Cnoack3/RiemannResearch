/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerMixedWavelet
import RiemannResearch.RH.QPrimePowerWaveletCoefficients
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Sparse mixed-prime coefficients of the floor-logarithm targets

Source: user-provided valuation-basis research direction, 20 October 2026.
The target remains Nat.log p n, not the prime valuation. Exact dilation and
Moebius cancellation eliminate mixed modes containing p and another prime.
The finite error identity retains all other modes in its norm-square residual.
Ambient mode removal is not asserted to preserve the legal squarefree closure.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity QDivisorHilbert

/-- Exact dilation by a p-power of any positive divisibility conductor. -/
theorem qTarget_scaled_primePower_divisor (p k d : ℕ) (hp : 1 < p) (hd : 0 < d) :
    ((p : ℝ) ^ k) ^ 2 * inner ℝ (qTarget p hp) (qDivisor (p ^ k * d)) =
      inner ℝ (qTarget p hp) (qDivisor d) + (k : ℝ) / (d : ℝ) ^ 2 := by
  have he : inversePowerMean 0 (fun n => qSequence (qTarget p hp) (p ^ k * d * n)) =
      inversePowerMean 0 (fun n => qSequence (qTarget p hp + (k : ℝ) • qOne) (d * n)) := by
    unfold inversePowerMean
    apply tsum_congr
    intro n
    have hdn : d * (n + 1) ≠ 0 := mul_ne_zero (ne_of_gt hd) (Nat.succ_ne_zero n)
    have hs : qSequence (qTarget p hp + (k : ℝ) • qOne) (d * (n + 1)) =
        (Nat.log p (d * (n + 1)) : ℝ) + k := by
      change qSequenceLinear (qTarget p hp + (k : ℝ) • qOne) (d * (n + 1)) = _
      simp [map_add, map_smul, qSequenceLinear, qTarget_sequence, qOneSequence, hdn]
    dsimp only
    rw [hs, qTarget_sequence]
    simp [mul_assoc, log_mul_power p k (d * (n + 1)) hp hdn, Nat.cast_add]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  calc
    _ = (1 / (d : ℝ) ^ 2) * inversePowerMean 0
        (fun n => qSequence (qTarget p hp + (k : ℝ) • qOne) (d * n)) := by
      rw [inner_qDivisor_eq_dilation _ _ (mul_pos (pow_pos (by omega) _) hd),
        he, Nat.cast_mul, Nat.cast_pow]
      field_simp
    _ = inner ℝ (qTarget p hp + (k : ℝ) • qOne) (qDivisor d) :=
      (inner_qDivisor_eq_dilation _ d hd).symm
    _ = _ := by
      rw [inner_add_left, real_inner_smul_left, qOne_inner_qDivisor d hd]
      ring

/-- All signed Möbius terms remain present until their exact cancellation. -/
theorem qTarget_inner_mixedPrimePowerWavelet_sum (p k r : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) (mixedPrimePowerWavelet p k r) =
      ∑ d ∈ r.divisors, (ArithmeticFunction.moebius (r / d) : ℝ) := by
  unfold mixedPrimePowerWavelet
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
  rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right,
    real_inner_smul_right, qTarget_scaled_primePower_divisor p (k + 1) d hp hdpos,
    qTarget_scaled_primePower_divisor p k d hp hdpos]
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- A nontrivial coprime cofactor kills the entire mixed wavelet coefficient. -/
theorem qTarget_inner_mixed_divisorWavelet (p k r : ℕ) (hp : p.Prime)
    (hr : 1 < r) (hpr : p.Coprime r) :
    inner ℝ (qTarget p hp.one_lt) (divisorWavelet (p ^ (k + 1) * r)) = 0 := by
  rw [divisorWavelet_primePower_mul p k r hp hpr,
    qTarget_inner_mixedPrimePowerWavelet_sum p k r hp.one_lt]
  calc
    (∑ d ∈ r.divisors, (ArithmeticFunction.moebius (r / d) : ℝ)) =
        ∑ a ∈ r.divisorsAntidiagonal, (ArithmeticFunction.moebius a.1 : ℝ) :=
      (Nat.sum_divisorsAntidiagonal' (fun a _ => (ArithmeticFunction.moebius a : ℝ))).symm
    _ = ∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℝ) :=
      Nat.sum_divisorsAntidiagonal (fun a _ => (ArithmeticFunction.moebius a : ℝ))
    _ = 0 := by
      change (∑ d ∈ r.divisors, (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d) = 0
      rw [← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_coe_moebius]
      simp [ne_of_gt hr]

/-- Normalization preserves the exact mixed-prime cancellation. -/
theorem qTarget_inner_normalizedDivisorWavelet_of_mixed (p : ℕ) (hp : p.Prime)
    (t : ℕ+) (k r : ℕ) (hr : 1 < r) (hpr : p.Coprime r)
    (ht : (t : ℕ) = p ^ (k + 1) * r) :
    inner ℝ (qTarget p hp.one_lt) (normalizedDivisorWavelet t) = 0 := by
  change inner ℝ (qTarget p hp.one_lt)
    ((Real.sqrt (qJordanTwo (t : ℕ)))⁻¹ • divisorWavelet (t : ℕ)) = 0
  rw [real_inner_smul_right, ht, qTarget_inner_mixed_divisorWavelet p k r hp hr hpr,
    mul_zero]

/-- Exact cost of unwanted mixed modes, retaining every other mode in the residual.
Removing these modes is an ambient operation; no preservation of the legal closure is claimed. -/
theorem qTarget_mixed_modes_error_exact (p : ℕ) (hp : p.Prime)
    (S : Finset ℕ+) (hS : ∀ t ∈ S, ∃ k r : ℕ,
      1 < r ∧ p.Coprime r ∧ (t : ℕ) = p ^ (k + 1) * r) (f : QHilbert) :
    ‖qTarget p hp.one_lt - f‖ ^ 2 =
      (∑ t ∈ S, (inner ℝ f (normalizedDivisorWavelet t)) ^ 2) +
      ‖qTarget p hp.one_lt - f + ∑ t ∈ S,
        inner ℝ f (normalizedDivisorWavelet t) • normalizedDivisorWavelet t‖ ^ 2 := by
  have hz (t : ℕ+) (ht : t ∈ S) :
      inner ℝ (qTarget p hp.one_lt) (normalizedDivisorWavelet t) = 0 := by
    rcases hS t ht with ⟨k, r, hr, hpr, he⟩
    exact qTarget_inner_normalizedDivisorWavelet_of_mixed p hp t k r hr hpr he
  have hn : ‖∑ t ∈ S, inner ℝ f (normalizedDivisorWavelet t) •
      normalizedDivisorWavelet t‖ ^ 2 =
      ∑ t ∈ S, (inner ℝ f (normalizedDivisorWavelet t)) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, normalizedDivisorWavelet_orthonormal.inner_sum]
    simp [pow_two]
  have hi : inner ℝ (qTarget p hp.one_lt - f)
      (∑ t ∈ S, inner ℝ f (normalizedDivisorWavelet t) • normalizedDivisorWavelet t) =
      -(∑ t ∈ S, (inner ℝ f (normalizedDivisorWavelet t)) ^ 2) := by
    rw [inner_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [real_inner_smul_right, inner_sub_left, hz t ht]
    ring
  rw [norm_add_sq_real, hn, hi]
  ring

end RiemannResearch.RH.PrimePowerTarget
