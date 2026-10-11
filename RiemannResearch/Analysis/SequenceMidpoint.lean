import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

/-!
# Midpoint cumulative coordinates and exact squared-energy summation

This file formalizes the elementary finite algebra in Sections 6.1 and 18 of
`V_Zeta_Zeros_Fourier_Chebyshev_Handoff_2026-09-16 (1).md`.

The index starts at zero. Thus `partialSum a N` contains the first `N` jump values.
No analytic convergence, zeta-zero location, or Riemann Hypothesis is assumed.
The weighted identity retains both the terminal contribution and the complete
square of the cumulative sum.
-/

open scoped BigOperators

namespace SequenceMidpoint

variable {K : Type*} [Field K] [CharZero K]

/-- Cumulative value before the jump at `n`. -/
def partialSum (a : ℕ → K) (n : ℕ) : K :=
  ∑ k ∈ Finset.range n, a k

/-- Cumulative midpoint value at the jump at `n`. -/
def midpoint (a : ℕ → K) (n : ℕ) : K :=
  partialSum a n + a n / 2

omit [CharZero K] in
@[simp] theorem partialSum_zero (a : ℕ → K) : partialSum a 0 = 0 := by
  simp [partialSum]

omit [CharZero K] in
theorem partialSum_succ (a : ℕ → K) (n : ℕ) :
    partialSum a (n + 1) = partialSum a n + a n := by
  simp [partialSum, Finset.sum_range_succ]

theorem midpoint_eq_average (a : ℕ → K) (n : ℕ) :
    midpoint a n = (partialSum a (n + 1) + partialSum a n) / 2 := by
  rw [midpoint, partialSum_succ]
  ring

theorem midpoint_difference (a : ℕ → K) (n : ℕ) :
    midpoint a (n + 1) - midpoint a n = (a n + a (n + 1)) / 2 := by
  simp only [midpoint, partialSum_succ]
  ring

/-- Recover the cumulative value before the `n`th jump from midpoint data. -/
def recoverPrefix (b : ℕ → K) : ℕ → K
  | 0 => 0
  | n + 1 => 2 * b n - recoverPrefix b n

/-- Exact coefficientwise inverse of the projected midpoint summation map. -/
def inverseMidpoint (b : ℕ → K) (n : ℕ) : K :=
  2 * (b n - recoverPrefix b n)

omit [CharZero K] in
theorem partialSum_inverseMidpoint (b : ℕ → K) (n : ℕ) :
    partialSum (inverseMidpoint b) n = recoverPrefix b n := by
  induction n with
  | zero => simp [recoverPrefix]
  | succ n ih =>
      rw [partialSum_succ, ih]
      simp only [inverseMidpoint, recoverPrefix]
      ring

theorem recoverPrefix_midpoint (a : ℕ → K) (n : ℕ) :
    recoverPrefix (midpoint a) n = partialSum a n := by
  induction n with
  | zero => simp [recoverPrefix]
  | succ n ih =>
      simp only [recoverPrefix, ih, midpoint, partialSum_succ]
      ring

theorem inverseMidpoint_midpoint (a : ℕ → K) :
    inverseMidpoint (midpoint a) = a := by
  funext n
  simp only [inverseMidpoint, recoverPrefix_midpoint, midpoint]
  ring

theorem midpoint_inverseMidpoint (b : ℕ → K) :
    midpoint (inverseMidpoint b) = b := by
  funext n
  simp only [midpoint, partialSum_inverseMidpoint, inverseMidpoint]
  ring

/-- Midpoint cumulative coordinates give an algebraic bijection of sequences. -/
def midpointEquiv : (ℕ → K) ≃ (ℕ → K) where
  toFun := midpoint
  invFun := inverseMidpoint
  left_inv := inverseMidpoint_midpoint
  right_inv := midpoint_inverseMidpoint

theorem midpoint_bijective : Function.Bijective (midpoint (K := K)) :=
  midpointEquiv.bijective

/-- The local identity responsible for the exact Chebyshev square formula. -/
theorem jump_mul_midpoint (a : ℕ → K) (n : ℕ) :
    a n * midpoint a n =
      (partialSum a (n + 1) ^ 2 - partialSum a n ^ 2) / 2 := by
  rw [midpoint, partialSum_succ]
  ring

/-- Exact finite telescope, without a positivity or support hypothesis. -/
theorem sum_jump_mul_midpoint (a : ℕ → K) (N : ℕ) :
    (∑ n ∈ Finset.range N, a n * midpoint a n) = partialSum a N ^ 2 / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, partialSum_succ]
      simp only [midpoint]
      ring

omit [CharZero K] in
/-- Finite summation by parts with the terminal endpoint retained. -/
theorem weighted_difference_sum (f w : ℕ → K) (N : ℕ) :
    (∑ n ∈ Finset.range N, (f (n + 1) - f n) * w n) =
      f N * w N - f 0 * w 0 +
        ∑ n ∈ Finset.range N, f (n + 1) * (w n - w (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- Weighted Chebyshev square identity, retaining the endpoint and full square. -/
theorem weighted_jump_mul_midpoint (a w : ℕ → K) (N : ℕ) :
    (∑ n ∈ Finset.range N, a n * midpoint a n * w n) =
      (partialSum a N ^ 2 / 2) * w N +
        ∑ n ∈ Finset.range N,
          (partialSum a (n + 1) ^ 2 / 2) * (w n - w (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [midpoint, partialSum_succ]
      ring

/-- Exact centered decomposition. The signed cross term and error square remain. -/
theorem centered_square (a q : ℕ → K) (n : ℕ) :
    partialSum a n ^ 2 / 2 = q n ^ 2 / 2 +
      q n * (partialSum a n - q n) + (partialSum a n - q n) ^ 2 / 2 := by
  ring

end SequenceMidpoint

open scoped BigOperators

namespace SequenceMidpoint

/-- The exact positive harmonic difference. -/
theorem harmonic_weight_difference (n : ℕ) :
    1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) =
      1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]
  ring

/-- Exact harmonic energy identity for arbitrary real jump data. The endpoint
is essential. With `a n = vonMangoldt (n+1) - 1`, this is the centered
Chebyshev identity in the handoff continuation. -/
theorem harmonic_midpoint_energy (a : ℕ → ℝ) (N : ℕ) :
    2 * (∑ n ∈ Finset.range N, a n * midpoint a n / ((n : ℝ) + 1)) =
      partialSum a N ^ 2 / ((N : ℝ) + 1) +
        ∑ n ∈ Finset.range N,
          partialSum a (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one, midpoint, partialSum_succ]
      have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
      have h3 : (N : ℝ) + 1 + 1 ≠ 0 := by positivity
      field_simp [h1, h2, h3]
      ring

/-- In particular the signed prime-versus-background sum is always nonnegative;
this fact supplies no asymptotic upper bound. -/
theorem harmonic_midpoint_energy_nonneg (a : ℕ → ℝ) (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.range N, a n * midpoint a n / ((n : ℝ) + 1) := by
  have h := harmonic_midpoint_energy a N
  have hright : 0 ≤ partialSum a N ^ 2 / ((N : ℝ) + 1) +
      ∑ n ∈ Finset.range N,
        partialSum a (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    apply add_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro n hn
      positivity
  have hleft : 0 ≤ 2 *
      (∑ n ∈ Finset.range N, a n * midpoint a n / ((n : ℝ) + 1)) := by
    rw [h]
    exact hright
  exact (mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)).mp hleft

end SequenceMidpoint
