/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.QPrimePowerOrthogonal
import RiemannResearch.RH.QDivisorWaveletOverlap
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# Exact prime-power wavelet coefficients of the floor-logarithm targets

Source: user-provided orthonormal-basis research direction, 20 October 2026.
The target is `Nat.log p n`, not the prime valuation. We compute its actual
Q inner products with every same-prime power mode of the existing complete
ambient divisor basis. No membership in the legal squarefree enclosure is
asserted, and the finite energy identity retains its full residual.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity QDivisorHilbert

private theorem log_mul_power (p k n : ℕ) (hp : 1 < p) (hn : n ≠ 0) :
    Nat.log p (p ^ k * n) = Nat.log p n + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hne : p ^ k * n ≠ 0 := mul_ne_zero (pow_ne_zero _ (by omega)) hn
    rw [pow_succ, mul_assoc, mul_comm p n, ← mul_assoc,
      Nat.log_mul_base hp hne, ih]
    omega

/-- Exact dilation moment, including the complete positive-integer tail. -/
theorem qTarget_inner_primePowerDivisor (p k : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) (qDivisor (p ^ k)) =
      (1 / ((p : ℝ) ^ k) ^ 2) * (inner ℝ (qTarget p hp) qOne + k) := by
  rw [inner_qDivisor_eq_dilation _ _ (pow_pos (by omega) _), Nat.cast_pow]
  have he : inversePowerMean 0 (fun n => qSequence (qTarget p hp) (p ^ k * n)) =
      inner ℝ (qTarget p hp + (k : ℝ) • qOne) qOne := by
    rw [qInner_eq_inversePowerMean]
    unfold inversePowerMean
    apply tsum_congr
    intro n
    have hs : qSequence (qTarget p hp + (k : ℝ) • qOne) (n + 1) =
        (Nat.log p (n + 1) : ℝ) + k := by
      change qSequenceLinear (qTarget p hp + (k : ℝ) • qOne) (n + 1) = _
      simp [map_add, map_smul, qSequenceLinear, qTarget_sequence, qOneSequence]
    dsimp only
    rw [hs, qTarget_sequence, qSequence_qOne]
    simp [qOneSequence, log_mul_power p k (n + 1) hp (Nat.succ_ne_zero n), Nat.cast_add]
  rw [he, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, qOne_norm_sq]
  ring

/-- Every nonconstant same-prime raw wavelet has floor-log coefficient exactly one. -/
theorem qTarget_inner_primePowerWavelet (p k : ℕ) (hp : p.Prime) :
    inner ℝ (qTarget p hp.one_lt) (divisorWavelet (p ^ (k + 1))) = 1 := by
  rw [divisorWavelet_prime_pow_succ p k hp, inner_sub_right,
    real_inner_smul_right, real_inner_smul_right,
    qTarget_inner_primePowerDivisor, qTarget_inner_primePowerDivisor]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The normalized coefficient is positive, with its exact Jordan weight. -/
theorem qTarget_inner_normalizedPrimePowerWavelet (p k : ℕ) (hp : p.Prime) :
    inner ℝ (qTarget p hp.one_lt)
      (QDivisorHilbert.normalizedDivisorWavelet ⟨p ^ (k + 1), pow_pos hp.pos _⟩) =
        (Real.sqrt (qJordanTwo (p ^ (k + 1))))⁻¹ := by
  change inner ℝ (qTarget p hp.one_lt)
    ((Real.sqrt (qJordanTwo (p ^ (k + 1))))⁻¹ • divisorWavelet (p ^ (k + 1))) = _
  rw [real_inner_smul_right,
    qTarget_inner_primePowerWavelet p k hp, mul_one]

/-- Explicit geometric decay of every same-prime normalized coefficient. -/
theorem qTarget_inner_primePowerFrame_succ (p k : ℕ) (hp : p.Prime) :
    inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k + 1)) =
      1 / ((p : ℝ) ^ k * Real.sqrt ((p : ℝ) ^ 2 - 1)) := by
  change inner ℝ (qTarget p hp.one_lt)
    (QDivisorHilbert.normalizedDivisorWavelet _) = _
  rw [qTarget_inner_normalizedPrimePowerWavelet p k hp,
    qJordanTwo_prime_pow p (k + 1) hp,
    valuationWaveletWeight_succ, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (pow_pos (by exact_mod_cast hp.pos) _), inv_eq_one_div]

/-- Literal signed expansion coefficients; index zero retains the target mean. -/
def primePowerCoefficient (p : ℕ) (hp : p.Prime) (k : ℕ) : ℝ :=
  if k = 0 then inner ℝ (qTarget p hp.one_lt) qOne
  else (Real.sqrt (qJordanTwo (p ^ k)))⁻¹

theorem qTarget_inner_primePowerFrame (p : ℕ) (hp : p.Prime) (k : ℕ) :
    inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp k) =
      primePowerCoefficient p hp k := by
  cases k with
  | zero => simp [primePowerCoefficient]
  | succ k =>
    simpa [primePowerFrame, primePowerCoefficient] using
      qTarget_inner_normalizedPrimePowerWavelet p k hp

/-- Exact finite expansion energy: the unexplained part remains a norm square. -/
theorem qTarget_primePower_energy_exact (p : ℕ) (hp : p.Prime) (S : Finset ℕ) :
    ‖qTarget p hp.one_lt‖ ^ 2 =
      (∑ k ∈ S, (primePowerCoefficient p hp k) ^ 2) +
        ‖qTarget p hp.one_lt -
          ∑ k ∈ S, primePowerCoefficient p hp k • primePowerFrame p hp k‖ ^ 2 := by
  have hn : ‖∑ k ∈ S, primePowerCoefficient p hp k • primePowerFrame p hp k‖ ^ 2 =
      ∑ k ∈ S, (primePowerCoefficient p hp k) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      (primePowerFrame_orthonormal p hp).inner_sum]
    simp [pow_two]
  have hi : inner ℝ (qTarget p hp.one_lt)
      (∑ k ∈ S, primePowerCoefficient p hp k • primePowerFrame p hp k) =
        ∑ k ∈ S, (primePowerCoefficient p hp k) ^ 2 := by
    rw [inner_sum]
    simp only [real_inner_smul_right, qTarget_inner_primePowerFrame, pow_two]
  rw [norm_sub_sq_real, hn, hi]
  ring

/-- Arbitrary signed trial coefficients retain every discrepancy and the full residual. -/
theorem qTarget_primePower_error_exact (p : ℕ) (hp : p.Prime)
    (S : Finset ℕ) (c : ℕ → ℝ) :
    ‖qTarget p hp.one_lt - ∑ k ∈ S, c k • primePowerFrame p hp k‖ ^ 2 =
      (∑ k ∈ S, (primePowerCoefficient p hp k - c k) ^ 2) +
        ‖qTarget p hp.one_lt -
          ∑ k ∈ S, primePowerCoefficient p hp k • primePowerFrame p hp k‖ ^ 2 := by
  have hn : ‖∑ k ∈ S, c k • primePowerFrame p hp k‖ ^ 2 =
      ∑ k ∈ S, (c k) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, (primePowerFrame_orthonormal p hp).inner_sum]
    simp [pow_two]
  have hi : inner ℝ (qTarget p hp.one_lt)
      (∑ k ∈ S, c k • primePowerFrame p hp k) =
        ∑ k ∈ S, c k * primePowerCoefficient p hp k := by
    rw [inner_sum]
    simp only [real_inner_smul_right, qTarget_inner_primePowerFrame]
  have he := qTarget_primePower_energy_exact p hp S
  have hs : (∑ k ∈ S, (primePowerCoefficient p hp k - c k) ^ 2) =
      (∑ k ∈ S, (primePowerCoefficient p hp k) ^ 2) -
        2 * (∑ k ∈ S, c k * primePowerCoefficient p hp k) +
        ∑ k ∈ S, (c k) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [norm_sub_sq_real, hn, hi, hs]
  linarith

end RiemannResearch.RH.PrimePowerTarget
