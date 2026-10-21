/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorWaveletFactorization
import RiemannResearch.RH.QDivisorWaveletDensity
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.Ring

/-!
# Mixed prime-power arithmetic wavelets

Source: user-provided valuation-basis research direction, 20 October 2026.
The coprime factorization is an exact identity in the actual Q Hilbert space.
Every signed Moebius term is retained in the adjacent-tail representation.
No legal squarefree-closure membership is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QDivisorHilbert
open ZetaTwoHilbert QDivisibilityDensity

/-- Adjacent p-power tails with all signed Möbius terms from the other conductor. -/
def mixedPrimePowerWavelet (p k r : ℕ) : QHilbert :=
  ∑ d ∈ r.divisors, ((ArithmeticFunction.moebius (r / d) : ℝ) * (d : ℝ) ^ 2) •
    (((p : ℝ) ^ (k + 1)) ^ 2 • qDivisor (p ^ (k + 1) * d) -
      ((p : ℝ) ^ k) ^ 2 • qDivisor (p ^ k * d))

/-- Coprime conductors identify the mixed tail difference with the actual basis wavelet. -/
theorem divisorWavelet_primePower_mul (p k r : ℕ) (hp : p.Prime)
    (hpr : p.Coprime r) :
    divisorWavelet (p ^ (k + 1) * r) = mixedPrimePowerWavelet p k r := by
  apply qSequence_injective
  funext n
  cases n with
  | zero => simp
  | succ n =>
    rw [qSequence_divisorWavelet_succ, ← divisorWaveletAF_apply,
      (divisorWaveletAF_multiplicative (n + 1)).map_mul_of_coprime (hpr.pow_left _),
      divisorWaveletAF_prime_pow_succ p k (n + 1) hp, divisorWaveletAF_apply]
    change _ = qSequenceLinear (mixedPrimePowerWavelet p k r) (n + 1)
    unfold mixedPrimePowerWavelet
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, map_sub, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    change _ = ∑ d ∈ r.divisors, _ *
      (((p : ℝ) ^ (k + 1)) ^ 2 * qSequence (qDivisor (p ^ (k + 1) * d)) (n + 1) -
        ((p : ℝ) ^ k) ^ 2 * qSequence (qDivisor (p ^ k * d)) (n + 1))
    unfold qDivisorWavelet qScaledDivisibilitySum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hpd : p.Coprime d := hpr.of_dvd_right (Nat.dvd_of_mem_divisors hd)
    have he (a : ℕ) : p ^ a * d ∣ n + 1 ↔ p ^ a ∣ n + 1 ∧ d ∣ n + 1 := by
      constructor
      · intro h
        exact ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩
      · intro h
        exact (hpd.pow_left a).mul_dvd_of_dvd_of_dvd h.1 h.2
    simp only [qSequence_qDivisor, positiveDivisor, Nat.succ_ne_zero, ↓reduceIte,
      scaledDivisorAF, ArithmeticFunction.coe_mk, Nat.cast_pow, he]
    by_cases h₁ : p ^ (k + 1) ∣ n + 1 <;>
      by_cases h₂ : p ^ k ∣ n + 1 <;>
      by_cases h₃ : d ∣ n + 1 <;> simp [h₁, h₂, h₃] <;> ring

end RiemannResearch.RH.QDivisorHilbert
