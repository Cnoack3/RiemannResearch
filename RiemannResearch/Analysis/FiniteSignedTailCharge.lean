import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Finite signed tail-charge algebra

This file contains finite identities only. No infinite summability, periodicity,
Ramanujan estimate, or RH hypothesis is assumed.

For the physical index convention in the paper, instantiate `a j` with
`c_k (j + 1)`, `b j` with `r (j + 1) / ((j + 1) * (j + 2))`, and `T j`
with the complete tail charge starting at physical site `j + 1`.
The boundary term in `finite_abel` is kept explicitly.

-/

open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteSignedTailCharge

variable {R : Type*} [CommRing R]

/-- The primitive with negative increments and initial value zero. -/
def primitive (a : ℕ → R) (n : ℕ) : R :=
  -∑ j ∈ Finset.range n, a j

@[simp] theorem primitive_zero (a : ℕ → R) : primitive a 0 = 0 := by
  simp [primitive]

theorem primitive_succ (a : ℕ → R) (n : ℕ) :
    primitive a (n + 1) = primitive a n - a n := by
  simp only [primitive, Finset.sum_range_succ]
  ring

/-- Exact finite signed Abel summation. `T N` is the endpoint charge. -/
theorem finite_abel (a T : ℕ → R) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      (T j - T (j + 1)) * primitive a (j + 1)) =
      -(∑ j ∈ Finset.range N, a j * T j) +
        T N * (∑ j ∈ Finset.range N, a j) := by
  unfold primitive
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ] at ih ⊢
      rw [ih]
      ring

/-- A source may be supplied by an arbitrary sequence of tail-charge differences. -/
theorem finite_source_of_tail_differences
    (a b T : ℕ → R) (N : ℕ)
    (hstep : ∀ j, j < N → b j = T j - T (j + 1)) :
    (∑ j ∈ Finset.range N, b j * primitive a (j + 1)) =
      -(∑ j ∈ Finset.range N, a j * T j) +
        T N * (∑ j ∈ Finset.range N, a j) := by
  calc
    (∑ j ∈ Finset.range N, b j * primitive a (j + 1)) =
        ∑ j ∈ Finset.range N,
          (T j - T (j + 1)) * primitive a (j + 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hstep j (Finset.mem_range.mp hj)]
    _ = _ := finite_abel a T N

/-- The same identity expressed with the endpoint primitive itself. -/
theorem finite_abel_endpoint (a T : ℕ → R) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      (T j - T (j + 1)) * primitive a (j + 1)) =
      -(∑ j ∈ Finset.range N, a j * T j) -
        T N * primitive a N := by
  rw [finite_abel]
  unfold primitive
  ring

/-- A finite tail represented as total mass minus its prefix.
For `n ≤ N`, this is the ordinary finite tail from `n` through `N - 1`.
The formula is defined for all `n`, keeping its difference law unconditional. -/
def finiteTail (b : ℕ → R) (N n : ℕ) : R :=
  (∑ j ∈ Finset.range N, b j) - ∑ j ∈ Finset.range n, b j

@[simp] theorem finiteTail_endpoint (b : ℕ → R) (N : ℕ) :
    finiteTail b N N = 0 := by
  simp [finiteTail]

theorem finiteTail_difference (b : ℕ → R) (N n : ℕ) :
    finiteTail b N n - finiteTail b N (n + 1) = b n := by
  simp only [finiteTail, Finset.sum_range_succ]
  ring

/-- Finite tail charges have zero endpoint, so their Abel identity has no
boundary remainder. This does not remove the boundary for infinite tails. -/
theorem finite_source_finiteTail (a b : ℕ → R) (N : ℕ) :
    (∑ j ∈ Finset.range N, b j * primitive a (j + 1)) =
      -(∑ j ∈ Finset.range N, a j * finiteTail b N j) := by
  have hstep : ∀ j, j < N →
      b j = finiteTail b N j - finiteTail b N (j + 1) := by
    intro j _
    exact (finiteTail_difference b N j).symm
  simpa only [finiteTail_endpoint, zero_mul, add_zero] using
    finite_source_of_tail_differences a b (finiteTail b N) N hstep

/-- Exact finite transport splitting, retaining the finite old-source term. -/
theorem transported_source_split
    (b old transported new : ℕ → R) (p : R) (N : ℕ)
    (hnew : ∀ j, j < N → new j = p * transported j - old j) :
    (∑ j ∈ Finset.range N, b j * new j) =
      p * (∑ j ∈ Finset.range N, b j * transported j) -
        (∑ j ∈ Finset.range N, b j * old j) := by
  calc
    (∑ j ∈ Finset.range N, b j * new j) =
        ∑ j ∈ Finset.range N,
          (p * (b j * transported j) - b j * old j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hnew j (Finset.mem_range.mp hj)]
            ring
    _ = p * (∑ j ∈ Finset.range N, b j * transported j) -
        (∑ j ∈ Finset.range N, b j * old j) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- Exact finite orthogonality cancellation when the finite old source is zero.
Infinite orthogonality does not imply this finite hypothesis at each cutoff;
use `transported_source_split` before passing to the limit in that setting. -/
theorem transported_source_of_old_source_zero
    (b old transported new : ℕ → R) (p : R) (N : ℕ)
    (hnew : ∀ j, j < N → new j = p * transported j - old j)
    (hold : (∑ j ∈ Finset.range N, b j * old j) = 0) :
    (∑ j ∈ Finset.range N, b j * new j) =
      p * (∑ j ∈ Finset.range N, b j * transported j) := by
  rw [transported_source_split b old transported new p N hnew, hold, sub_zero]

end RiemannResearch.Analysis.FiniteSignedTailCharge
