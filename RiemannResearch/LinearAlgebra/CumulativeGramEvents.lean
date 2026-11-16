import RiemannResearch.LinearAlgebra.WeightedGreenInverse
import Mathlib.Tactic.Ring

/-!
# Event accumulation for cumulative weighted Gram matrices
Source: independent finite summation - by - parts derivation for agenda R1 / R2 in
the user - provided "Exact - Head Green Profiles in the Nyman--Beurling Program",
27 July 2026. This validates the algebra used by the retained event - accumulation
experiment. It does not verify floating - point digamma evaluation or the C++ code.
Both mixed terms and the simultaneous - jump term are retained, for signed weights.
-/
open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.WeightedGreen
noncomputable section

theorem prefix_initialDifference (f : ℕ → ℝ) (k : ℕ) :
    greenPrefix (initialDifference f) k = f k := by
  induction k with
  | zero => simp [greenPrefix, initialDifference]
  | succ k ih =>
    change (∑ j ∈ Finset.range (k + 1 + 1), initialDifference f j) = _
    rw [Finset.sum_range_succ]
    change greenPrefix (initialDifference f) k + (f (k + 1) - f k) = f (k + 1)
    rw [ih]
    ring

/-- Finite summation by parts with the full terminal tail. -/
theorem weighted_sum_eq_tail_difference (N : ℕ) (w f : ℕ → ℝ) :
    (∑ k ∈ Finset.range N, w k * f k) =
      ∑ i ∈ Finset.range N, tail N w i * initialDifference f i := by
  symm
  simp only [tail, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = w k * (∑ i ∈ Finset.range N, if i ≤ k then initialDifference f i else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i ≤ k <;> simp [h]
    _ = w k * greenPrefix (initialDifference f) k := by
      rw [truncated_prefix N _ k (Finset.mem_range.mp hk)]
    _ = _ := by rw [prefix_initialDifference]

theorem cumulative_product_jump (a b : ℕ → ℝ) (i : ℕ) :
    initialDifference (fun k => greenPrefix a k * greenPrefix b k) i =
      a i * (∑ j ∈ Finset.range i, b j) +
      b i * (∑ j ∈ Finset.range i, a j) + a i * b i := by
  cases i with
  | zero => simp [initialDifference, greenPrefix]
  | succ i =>
    simp only [initialDifference, greenPrefix, Finset.sum_range_succ]
    ring

/-- Each event contributes its two cross terms and the jump - product correction. -/
theorem cumulative_gram_event_identity (N : ℕ) (w a b : ℕ → ℝ) :
    (∑ k ∈ Finset.range N, w k * greenPrefix a k * greenPrefix b k) =
      ∑ i ∈ Finset.range N, tail N w i *
        (a i * (∑ j ∈ Finset.range i, b j) +
         b i * (∑ j ∈ Finset.range i, a j) + a i * b i) := by
  have h := weighted_sum_eq_tail_difference N w
    (fun k => greenPrefix a k * greenPrefix b k)
  simpa only [cumulative_product_jump, mul_assoc] using h

theorem cumulative_energy_event_identity (N : ℕ) (w a : ℕ → ℝ) :
    (∑ k ∈ Finset.range N, w k * (greenPrefix a k) ^ 2) =
      ∑ i ∈ Finset.range N, tail N w i *
        (2 * a i * (∑ j ∈ Finset.range i, a j) + a i ^ 2) := by
  have h := cumulative_gram_event_identity N w a a
  convert h using 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

end
end RiemannResearch.LinearAlgebra.WeightedGreen
