/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusFullEnergy

/-!
# Linear complete error ceiling for canonical exact heads

An exact physical head removes the entire finite-head contribution to the
error norm. The complete infinite tail is then bounded using the actual
canonical pointwise bound. This discharges the historical linear exact-head
upper-witness target, and improves the existing coarse error bound 8N+2.
No subpower or vanishing optimized error estimate is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- A pointwise bound and an exact head give an upper bound for the complete
infinite approximation error. Only the tail has nonzero error. -/
theorem exactHead_bounded_completeError_upper
    (f : ThresholdHilbert) (N : ℕ) (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ n, |hilbertSequence f n| ≤ C)
    (hhead : ∀ n, 0 < n → n ≤ N → hilbertSequence f n = 1) :
    ‖hilbertOne - f‖ ^ 2 ≤ (C + 1) ^ 2 / ((N : ℝ) + 1) := by
  have hsub (k : ℕ) :
      hilbertSequence (hilbertOne - f) k =
        hilbertSequence hilbertOne k - hilbertSequence f k :=
    congrFun (map_sub hilbertSequenceLinear hilbertOne f) k
  have hs := hilbertSequence_square_summable (hilbertOne - f)
  have ht := (summable_nat_add_iff (N + 1)).mpr hs
  have hw := (summable_nat_add_iff (N + 1)).mpr positiveWeight_summable
  rw [hilbert_norm_weighted_sq, ← hs.sum_add_tsum_nat_add (N + 1)]
  have hzero : (∑ k ∈ Finset.range (N + 1), positiveWeight k *
      hilbertSequence (hilbertOne - f) k ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0, positiveWeight]
    · have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
      rw [hsub, hhead k (by omega) hkN,
        hilbertOne_sequence]
      simp [zeroAnchor, hk0]
  rw [hzero, zero_add]
  calc
    _ ≤ ∑' k : ℕ, positiveWeight (k + (N + 1)) * (C + 1) ^ 2 := by
      apply Summable.tsum_le_tsum _ ht (hw.mul_right ((C + 1) ^ 2))
      intro k
      apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
      rw [hsub, hilbertOne_sequence]
      have hk0 : k + (N + 1) ≠ 0 := by omega
      simp only [zeroAnchor, if_neg hk0]
      have ha : |1 - hilbertSequence f (k + (N + 1))| ≤ C + 1 := by
        calc
          _ ≤ |(1 : ℝ)| + |hilbertSequence f (k + (N + 1))| := by
            simpa only [Real.norm_eq_abs] using
              norm_sub_le (1 : ℝ) (hilbertSequence f (k + (N + 1)))
          _ ≤ _ := by simpa only [abs_one, add_comm] using
            add_le_add_left (hbound (k + (N + 1))) 1
      have hsq := mul_self_le_mul_self (abs_nonneg _) ha
      simpa only [← pow_two, sq_abs] using hsq
    _ = (C + 1) ^ 2 / ((N : ℝ) + 1) := by
      rw [tsum_mul_right, positiveWeight_tail_tsum (N + 1) (Nat.succ_pos _)]
      push_cast
      ring

/-- The canonical competitor supplies the exact requested historical
linear ceiling, with the complete infinite residual energy. -/
theorem canonicalMobiusResidual_norm_sq_le_linear_ceiling
    (N : ℕ) (hN : 0 < N) :
    ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 ≤
      4 * (N : ℝ) + 1 / ((N : ℝ) + 1) := by
  have h := exactHead_bounded_completeError_upper (canonicalMobiusHilbert N) N
    (2 * (N : ℝ)) (by positivity)
    (fun n => by rw [canonicalMobiusHilbert_sequence]; exact
      canonicalMobiusHead_abs_le_two_mul N hN n)
    (canonicalMobiusHilbert_exact N)
  have he : (2 * (N : ℝ) + 1) ^ 2 / ((N : ℝ) + 1) =
      4 * (N : ℝ) + 1 / ((N : ℝ) + 1) := by
    have hn : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn]
    ring
  rwa [he] at h


end RiemannResearch.RH.Pareto
