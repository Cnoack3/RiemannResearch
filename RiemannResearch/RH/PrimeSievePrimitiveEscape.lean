/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimeSieveDerivativeClosure

/-!
# The actual derivative sieve escapes in primitive norm

The legal sieve has a vanishing full derivative error, but its primitive
energy diverges. Exact finite-head plus full-tail identities precede the
lower bound. In particular, derivative convergence is not primitive convergence.

Source: the user-directed vanishing attempt, continuing
`CRTPrimitiveTransferAudit20260929.md`, Section 6, and the existing
repository dyadic and arithmetic identities.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto

theorem derivativeSievePrimitive_head (Y k : ℕ) (hk : 0 < k) (hkY : k ≤ Y) :
    derivativeSievePrimitive Y k = 1 - sieveReciprocal Y.factorial * (k : ℝ) := by
  rw [derivativeSievePrimitive, sieveResidue_exact _ _ _ (Nat.factorial_pos Y) (by decide)]
  simp only [Nat.cast_one, div_one, Nat.div_one,
    sieveRoughCount_factorial_head Y k hk hkY]
  ring

/-- The complete primitive tail beyond the arithmetic head. -/
def derivativeSievePrimitiveTailEnergy (Y : ℕ) : ℝ :=
  ∑' j : ℕ, positiveWeight (j + (Y + 1)) *
    (derivativeSievePrimitive Y (j + (Y + 1))) ^ 2

/-- The complete error tail beyond the arithmetic head. -/
def derivativeSievePrimitiveErrorTailEnergy (Y : ℕ) : ℝ :=
  ∑' j : ℕ, positiveWeight (j + (Y + 1)) *
    (1 - derivativeSievePrimitive Y (j + (Y + 1))) ^ 2

theorem derivativeSievePrimitiveTailEnergy_nonneg (Y : ℕ) :
    0 ≤ derivativeSievePrimitiveTailEnergy Y :=
  tsum_nonneg fun _j => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _)

theorem derivativeSievePrimitiveErrorTailEnergy_nonneg (Y : ℕ) :
    0 ≤ derivativeSievePrimitiveErrorTailEnergy Y :=
  tsum_nonneg fun _j => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _)

/-- Every head square and every term of the infinite tail is retained. -/
theorem derivativeSieveHilbert_norm_sq_exact (Y : ℕ) :
    ‖derivativeSieveHilbert Y‖ ^ 2 =
      (∑ j ∈ Finset.range Y, positiveWeight (j + 1) *
        (1 - sieveReciprocal Y.factorial * ((j + 1 : ℕ) : ℝ)) ^ 2) +
      derivativeSievePrimitiveTailEnergy Y := by
  have hs := (hilbertSequence_square_summable
    (derivativeSieveHilbert Y)).sum_add_tsum_nat_add (Y + 1)
  rw [← hilbert_norm_weighted_sq, derivativeSieveHilbert_sequence] at hs
  rw [← hs, Finset.sum_range_succ']
  have hz : positiveWeight 0 * derivativeSievePrimitive Y 0 ^ 2 = 0 := by simp
  rw [hz, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [derivativeSievePrimitive_head Y (j + 1) (by omega)
    (by have := Finset.mem_range.mp hj; omega)]

theorem derivativeSieveHilbert_primitive_error_sequence (Y k : ℕ) (hk : 0 < k) :
    hilbertSequence (hilbertOne - derivativeSieveHilbert Y) k =
      1 - derivativeSievePrimitive Y k := by
  rw [hilbertSequence_sub, derivativeSieveHilbert_sequence, hilbertOne_sequence]
  simp [zeroAnchor, Nat.ne_of_gt hk]

private theorem primitive_head_error_coordinate (Y j : ℕ) :
    positiveWeight (j + 1) *
      (sieveReciprocal Y.factorial * ((j + 1 : ℕ) : ℝ)) ^ 2 =
      (sieveReciprocal Y.factorial) ^ 2 *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) := by
  unfold positiveWeight
  push_cast
  have h₁ : (j : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (j : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Exact error head and complete error tail. The head alone is divergent. -/
theorem derivativeSieveHilbert_primitive_error_exact (Y : ℕ) :
    ‖hilbertOne - derivativeSieveHilbert Y‖ ^ 2 =
      (sieveReciprocal Y.factorial) ^ 2 *
        (∑ j ∈ Finset.range Y, ((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) +
      derivativeSievePrimitiveErrorTailEnergy Y := by
  have hs := (hilbertSequence_square_summable
    (hilbertOne - derivativeSieveHilbert Y)).sum_add_tsum_nat_add (Y + 1)
  rw [← hilbert_norm_weighted_sq] at hs
  rw [← hs, Finset.sum_range_succ']
  have hz : positiveWeight 0 *
      hilbertSequence (hilbertOne - derivativeSieveHilbert Y) 0 ^ 2 = 0 := by
    simp [positiveWeight]
  rw [hz, add_zero, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [derivativeSieveHilbert_primitive_error_sequence Y (j + 1) (by omega),
      derivativeSievePrimitive_head Y (j + 1) (by omega)
        (by have := Finset.mem_range.mp hj; omega)]
    simpa only [sub_sub_cancel] using primitive_head_error_coordinate Y j
  · unfold derivativeSievePrimitiveErrorTailEnergy
    apply tsum_congr
    intro j
    rw [derivativeSieveHilbert_primitive_error_sequence Y (j + (Y + 1)) (by omega)]

theorem derivativeSieveHilbert_primitive_error_lower (Y : ℕ) :
    (sieveReciprocal Y.factorial) ^ 2 * (Y : ℝ) / 2 ≤
      ‖hilbertOne - derivativeSieveHilbert Y‖ ^ 2 := by
  have hh : (Y : ℝ) / 2 ≤
      ∑ j ∈ Finset.range Y, ((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ) := by
    calc
      _ = ∑ _j ∈ Finset.range Y, (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((j + 2 : ℕ) : ℝ))).2
        push_cast
        nlinarith [show (0 : ℝ) ≤ j by positivity]
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg (sieveReciprocal Y.factorial))
  rw [derivativeSieveHilbert_primitive_error_exact]
  nlinarith [derivativeSievePrimitiveErrorTailEnergy_nonneg Y]

/-- A dimension-free lower bound on the actual primitive norm. -/
theorem derivativeSieveHilbert_norm_sq_lower (Y : ℕ) :
    (sieveReciprocal Y.factorial) ^ 2 * (Y : ℝ) / 4 ≤
      ‖derivativeSieveHilbert Y‖ ^ 2 + 1 := by
  have ht := norm_sub_le hilbertOne (derivativeSieveHilbert Y)
  have hsq := mul_self_le_mul_self
    (norm_nonneg (hilbertOne - derivativeSieveHilbert Y)) ht
  have he := derivativeSieveHilbert_primitive_error_lower Y
  have hone := hilbertOne_norm_sq
  nlinarith [sq_nonneg (‖hilbertOne‖ - ‖derivativeSieveHilbert Y‖)]

/-- Unconditional escape of this exact legal sieve, despite derivative error vanishing. -/
theorem derivativeSieveHilbert_norm_sq_tendsto_atTop :
    Tendsto (fun Y : ℕ => ‖derivativeSieveHilbert Y‖ ^ 2) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_atTop.1
    factorialSieveReciprocal_square_mul_tendsto_atTop) (4 * (b + 1))] with Y hY
  nlinarith [derivativeSieveHilbert_norm_sq_lower Y]

theorem derivativeSieveHilbert_primitive_error_tendsto_atTop :
    Tendsto (fun Y : ℕ => ‖hilbertOne - derivativeSieveHilbert Y‖ ^ 2)
      atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_atTop.1
    factorialSieveReciprocal_square_mul_tendsto_atTop) (2 * b)] with Y hY
  nlinarith [derivativeSieveHilbert_primitive_error_lower Y]

theorem derivativeSieveHilbert_norm_tendsto_atTop :
    Tendsto (fun Y : ℕ => ‖derivativeSieveHilbert Y‖) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_atTop.1 derivativeSieveHilbert_norm_sq_tendsto_atTop)
    ((max b 0) ^ 2)] with Y hY
  have hb := le_max_left b 0
  have hb0 := le_max_right b 0
  nlinarith [norm_nonneg (derivativeSieveHilbert Y)]

end RiemannResearch.RH.Pareto
