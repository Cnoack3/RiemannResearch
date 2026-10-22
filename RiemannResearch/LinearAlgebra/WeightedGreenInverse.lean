import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite weighted Green inverse, retaining the last weight

Source: user-provided periodic Green / Schur calculation, 22 September 2026.
The calculation supports the kernel, inverse coefficients and proof strategy.

Indices are zero-based: i,j = 0,...,N-1.
K(i,j) = sum_{max(i,j) <= k < N} w(k).
The right boundary is y(N)=0.  All N weights are retained.

For the zero-boundary period-L Pareto kernel substitute N=L-1 and w(i)=W_L(i+1).
The zero-total-charge packet subspace requires no change to the generic
positive Green kernel or to its right boundary.
-/

open scoped BigOperators

namespace RiemannResearch.LinearAlgebra.WeightedGreen

noncomputable section

def greenPrefix (a : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (i + 1), a j

def tail (N : ℕ) (a : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, if i ≤ k then a k else 0

def kernel (N : ℕ) (w : ℕ → ℝ) (i j : ℕ) : ℝ :=
  tail N w (max i j)

def applyGreen (N : ℕ) (w c : ℕ → ℝ) (i : ℕ) : ℝ :=
  tail N (fun k => w k * greenPrefix c k) i

def initialDifference (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => a 0
  | i + 1 => a (i + 1) - a i

def flux (w y : ℕ → ℝ) (i : ℕ) : ℝ :=
  (y i - y (i + 1)) / w i

def applyInverse (w y : ℕ → ℝ) (i : ℕ) : ℝ :=
  initialDifference (flux w y) i

theorem prefix_zero (c : ℕ → ℝ) : greenPrefix c 0 = c 0 := by
  simp [greenPrefix]

theorem prefix_difference (c : ℕ → ℝ) (i : ℕ) :
    greenPrefix c (i + 1) - greenPrefix c i = c (i + 1) := by
  simp only [greenPrefix, Finset.sum_range_succ]
  ring

theorem initialDifference_prefix (c : ℕ → ℝ) (i : ℕ) :
    initialDifference (greenPrefix c) i = c i := by
  cases i with
  | zero => exact prefix_zero c
  | succ i => exact prefix_difference c i

theorem truncated_prefix (N : ℕ) (c : ℕ → ℝ) (k : ℕ) (hk : k < N) :
    (∑ j ∈ Finset.range N, if j ≤ k then c j else 0) = greenPrefix c k := by
  rw [← Finset.sum_filter]
  unfold greenPrefix
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem tail_difference (N : ℕ) (a : ℕ → ℝ) (i : ℕ) (hi : i < N) :
    tail N a i - tail N a (i + 1) = a i := by
  unfold tail
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k hk hki
    by_cases hik : i ≤ k
    · have hik' : i + 1 ≤ k := by omega
      simp [hik, hik']
    · have hik' : ¬ i + 1 ≤ k := by omega
      simp [hik, hik']
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hi))

theorem tail_right_boundary (N : ℕ) (a : ℕ → ℝ) : tail N a N = 0 := by
  unfold tail
  apply Finset.sum_eq_zero
  intro k hk
  have hk' : k < N := Finset.mem_range.mp hk
  have h : ¬ N ≤ k := by omega
  simp [h]

theorem applyGreen_right_boundary (N : ℕ) (w c : ℕ → ℝ) :
    applyGreen N w c N = 0 := by
  exact tail_right_boundary N (fun k => w k * greenPrefix c k)

theorem applyGreen_difference (N : ℕ) (w c : ℕ → ℝ) (i : ℕ) (hi : i < N) :
    applyGreen N w c i - applyGreen N w c (i + 1) = w i * greenPrefix c i := by
  exact tail_difference N (fun k => w k * greenPrefix c k) i hi

/-- The finite tail-of-prefix operator is multiplication by the stated kernel. -/
theorem applyGreen_eq_kernel_sum (N : ℕ) (w c : ℕ → ℝ) (i : ℕ) :
    applyGreen N w c i =
      ∑ j ∈ Finset.range N, kernel N w i j * c j := by
  unfold applyGreen tail
  calc
    _ = ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range N,
        if max i j ≤ k then w k * c j else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only
      rw [← truncated_prefix N c k (Finset.mem_range.mp hk)]
      by_cases hik : i ≤ k
      · simp only [if_pos hik, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hjk : j ≤ k
        · simp [hik, hjk]
        · simp [hik, hjk]
      · simp only [if_neg hik]
        symm
        apply Finset.sum_eq_zero
        intro j _
        have hmax : ¬ max i j ≤ k := by simp [hik]
        simp [hmax]
    _ = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        if max i j ≤ k then w k * c j else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [kernel, tail, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : max i j ≤ k <;> simp [h]

theorem flux_applyGreen (N : ℕ) (w c : ℕ → ℝ)
    (hw : ∀ i, i < N → w i ≠ 0) (i : ℕ) (hi : i < N) :
    flux w (applyGreen N w c) i = greenPrefix c i := by
  unfold flux
  rw [applyGreen_difference N w c i hi]
  field_simp [hw i hi]

/-- The one-sided difference of weighted flux is the inverse Green action. -/
theorem applyInverse_applyGreen (N : ℕ) (w c : ℕ → ℝ)
    (hw : ∀ i, i < N → w i ≠ 0) (i : ℕ) (hi : i < N) :
    applyInverse w (applyGreen N w c) i = c i := by
  cases i with
  | zero =>
    simp only [applyInverse, initialDifference]
    rw [flux_applyGreen N w c hw 0 hi]
    exact prefix_zero c
  | succ i =>
    simp only [applyInverse, initialDifference]
    rw [flux_applyGreen N w c hw (i + 1) hi,
      flux_applyGreen N w c hw i (by omega)]
    exact prefix_difference c i

theorem inverse_left_row (w y : ℕ → ℝ) :
    applyInverse w y 0 = (y 0 - y 1) / w 0 := by
  rfl

/-- Every row after the first has the exact tridiagonal coefficients. -/
theorem inverse_tridiagonal_row (w y : ℕ → ℝ) (i : ℕ) :
    applyInverse w y (i + 1) =
      -(w i)⁻¹ * y i + ((w i)⁻¹ + (w (i + 1))⁻¹) * y (i + 1)
        - (w (i + 1))⁻¹ * y (i + 2) := by
  simp only [applyInverse, initialDifference, flux, div_eq_mul_inv]
  ring

/-- The finite Green bilinear form is the weighted product of cumulative charges. -/
theorem green_bilinear_identity (N : ℕ) (w c d : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, c i * applyGreen N w d i) =
      ∑ k ∈ Finset.range N, w k * greenPrefix c k * greenPrefix d k := by
  simp only [applyGreen, tail, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = (∑ i ∈ Finset.range N, if i ≤ k then c i else 0) *
        (w k * greenPrefix d k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i ≤ k <;> simp [h]
    _ = _ := by
      rw [truncated_prefix N c k (Finset.mem_range.mp hk)]
      ring

/-- The inverse quadratic form has an exact weighted Dirichlet representation. -/
theorem green_dirichlet_identity (N : ℕ) (w c : ℕ → ℝ)
    (hw : ∀ i, i < N → w i ≠ 0) :
    (∑ i ∈ Finset.range N, c i * applyGreen N w c i) =
      ∑ i ∈ Finset.range N,
        (applyGreen N w c i - applyGreen N w c (i + 1)) ^ 2 / w i := by
  rw [green_bilinear_identity]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < N := Finset.mem_range.mp hi
  rw [applyGreen_difference N w c i hi']
  field_simp [hw i hi']

end

end RiemannResearch.LinearAlgebra.WeightedGreen
