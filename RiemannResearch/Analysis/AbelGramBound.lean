import RiemannResearch.Analysis.AbelOrbitGrowth
import RiemannResearch.Analysis.AbelPrefixBound
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform Abel norm bounds from complete Gram data

Source: user-provided quotient norm handoff, (N26)--(N30). We retain the exact
squared-norm recurrence before estimating every cross term. A nonnegative
majorant of the off-diagonal Gram entries with linearly bounded prefix sums
suffices. No independence or orthogonality of distinct orbit vectors is used.

The uniform bound `D + 2*A` is deliberately not the sharper diagonal tracking
in (N30); it proves the required boundedness with a simpler finite recurrence.
-/

open scoped BigOperators Topology
open Filter

namespace RiemannResearch.Analysis.AbelGram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def partialSum (r : ℝ) (v : ℕ → E) (N : ℕ) : E :=
  ∑ j ∈ Finset.range N, r ^ j • v j

/-- Reversing an off-diagonal row places it inside the complete prefix. -/
theorem reflected_sum_le_prefix (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (N : ℕ) :
    (∑ j ∈ Finset.range N, a (N - j)) ≤ prefixSum a (N + 1) := by
  have href : (∑ j ∈ Finset.range N, a (N - j)) =
      ∑ j ∈ Finset.range N, a (j + 1) := by
    calc
      (∑ j ∈ Finset.range N, a (N - j)) =
          ∑ j ∈ Finset.range N, a ((N - 1 - j) + 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjN := Finset.mem_range.mp hj
        congr 1
        omega
      _ = ∑ j ∈ Finset.range N, a (j + 1) :=
        Finset.sum_range_reflect (fun j => a (j + 1)) N
  rw [href, prefixSum, Finset.sum_range_succ']
  exact le_add_of_nonneg_right (ha 0)

/-- A complete off-diagonal row is bounded using its actual Gram entries. -/
theorem inner_partialSum_le
    (r A : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (v : ℕ → E)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hprefix : ∀ N, prefixSum a N ≤ A * N)
    (hoff : ∀ j k, j < k → |inner ℝ (v j) (v k)| ≤ a (k - j)) (N : ℕ) :
    inner ℝ (partialSum r v N) (v N) ≤ A * ((N : ℝ) + 1) := by
  have hrow : inner ℝ (partialSum r v N) (v N) ≤
      ∑ j ∈ Finset.range N, a (N - j) := by
    rw [partialSum, sum_inner]
    apply Finset.sum_le_sum
    intro j hj
    have hjN := Finset.mem_range.mp hj
    rw [real_inner_smul_left]
    have hpow0 : 0 ≤ r ^ j := pow_nonneg hr0 j
    have hpow1 : r ^ j ≤ 1 := pow_le_one₀ hr0 hr1
    calc
      r ^ j * inner ℝ (v j) (v N) ≤ r ^ j * a (N - j) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hoff j N hjN)) hpow0
      _ ≤ 1 * a (N - j) := mul_le_mul_of_nonneg_right hpow1 (ha (N - j))
      _ = a (N - j) := one_mul _
  have hp := hprefix (N + 1)
  norm_num only [Nat.cast_add, Nat.cast_one] at hp
  exact hrow.trans ((reflected_sum_le_prefix a ha N).trans hp)

/-- The exact finite scalar moment, including its terminal term. -/
theorem normalized_moment_prefix_eq (r : ℝ) (N : ℕ) :
    (1 - r) ^ 2 * (∑ j ∈ Finset.range N, r ^ j * ((j : ℝ) + 1)) =
      1 - r ^ N * (1 + (N : ℝ) * (1 - r)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      push_cast
      ring

theorem normalized_moment_prefix_le_one
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (N : ℕ) :
    (1 - r) ^ 2 * (∑ j ∈ Finset.range N, r ^ j * ((j : ℝ) + 1)) ≤ 1 := by
  rw [normalized_moment_prefix_eq]
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hprod : 0 ≤ r ^ N * (1 + (N : ℝ) * (1 - r)) := by
    exact mul_nonneg (pow_nonneg hr0 N)
      (by nlinarith [mul_nonneg hN (sub_nonneg.mpr hr1)])
  linarith

/-- Finite full-energy estimate from the diagonal and every off-diagonal
Gram entry. The proof starts with the exact norm-square recurrence. -/
theorem norm_partialSum_sq_le
    (r D A : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (v : ℕ → E) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hdiag : ∀ j, ‖v j‖ ^ 2 ≤ D * ((j : ℝ) + 1))
    (hprefix : ∀ N, prefixSum a N ≤ A * N)
    (hoff : ∀ j k, j < k → |inner ℝ (v j) (v k)| ≤ a (k - j)) (N : ℕ) :
    ‖partialSum r v N‖ ^ 2 ≤
      (D + 2 * A) * (∑ j ∈ Finset.range N, r ^ j * ((j : ℝ) + 1)) := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
      have hpow0 : 0 ≤ r ^ N := pow_nonneg hr0 N
      have hpow1 : r ^ N ≤ 1 := pow_le_one₀ hr0 hr1
      have hpowsq : (r ^ N) ^ 2 ≤ r ^ N := by
        nlinarith [mul_nonneg hpow0 (sub_nonneg.mpr hpow1)]
      have hdiagw : (r ^ N) ^ 2 * ‖v N‖ ^ 2 ≤ r ^ N * (D * ((N : ℝ) + 1)) := by
        calc
          (r ^ N) ^ 2 * ‖v N‖ ^ 2 ≤ (r ^ N) ^ 2 * (D * ((N : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (hdiag N) (sq_nonneg _)
          _ ≤ r ^ N * (D * ((N : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hpowsq (by positivity)
      have hcross := mul_le_mul_of_nonneg_left
        (inner_partialSum_le r A hr0 hr1 v a ha hprefix hoff N) hpow0
      have hrec : partialSum r v (N + 1) = partialSum r v N + r ^ N • v N := by
        simp only [partialSum, Finset.sum_range_succ]
      rw [hrec, norm_add_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hpow0, mul_pow, Finset.sum_range_succ]
      nlinarith

/-- Uniform finite Abel norm estimate with every mixed term included. -/
theorem norm_finite_average_sq_le
    (r D A : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (v : ℕ → E) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hdiag : ∀ j, ‖v j‖ ^ 2 ≤ D * ((j : ℝ) + 1))
    (hprefix : ∀ N, prefixSum a N ≤ A * N)
    (hoff : ∀ j k, j < k → |inner ℝ (v j) (v k)| ≤ a (k - j)) (N : ℕ) :
    ‖(1 - r) • partialSum r v N‖ ^ 2 ≤ D + 2 * A := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr1), mul_pow]
  calc
    (1 - r) ^ 2 * ‖partialSum r v N‖ ^ 2 ≤
        (1 - r) ^ 2 * ((D + 2 * A) *
          (∑ j ∈ Finset.range N, r ^ j * ((j : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left
        (norm_partialSum_sq_le r D A hr0 hr1 hD hA v a ha hdiag hprefix hoff N)
        (sq_nonneg _)
    _ = (D + 2 * A) * ((1 - r) ^ 2 *
        (∑ j ∈ Finset.range N, r ^ j * ((j : ℝ) + 1))) := by ring
    _ ≤ (D + 2 * A) * 1 := mul_le_mul_of_nonneg_left
      (normalized_moment_prefix_le_one r hr0 hr1 N) (by positivity)
    _ = D + 2 * A := mul_one _

variable [CompleteSpace E]

/-- Diagonal Gram growth already gives absolute convergence of the vector
series; summability is not assumed in the final theorem. -/
theorem summable_geometric_of_diagonal
    (r D : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hD : 0 ≤ D) (v : ℕ → E)
    (hdiag : ∀ j, ‖v j‖ ^ 2 ≤ D * ((j : ℝ) + 1)) :
    Summable (fun j : ℕ => r ^ j • v j) := by
  apply AbelCoboundary.summable_geometric_of_sqrt_growth
    r (Real.sqrt D) hr0 hr1 (Real.sqrt_nonneg _) v
  intro j
  have hj0 : 0 ≤ (j : ℝ) + 1 := by positivity
  have hprod : (Real.sqrt D * Real.sqrt ((j : ℝ) + 1)) ^ 2 =
      D * ((j : ℝ) + 1) := by
    rw [mul_pow, Real.sq_sqrt hD, Real.sq_sqrt hj0]
  have hnonneg : 0 ≤ Real.sqrt D * Real.sqrt ((j : ℝ) + 1) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq := hdiag j
  nlinarith [norm_nonneg (v j)]

/-- Uniform infinite Abel norm bound obtained from complete mathematical Gram
data. The off-diagonal hypothesis is stated on the upper triangle, since real
inner-product symmetry supplies the lower triangle in the exact recurrence. -/
theorem norm_average_sq_le
    (r D A : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (v : ℕ → E) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hdiag : ∀ j, ‖v j‖ ^ 2 ≤ D * ((j : ℝ) + 1))
    (hprefix : ∀ N, prefixSum a N ≤ A * N)
    (hoff : ∀ j k, j < k → |inner ℝ (v j) (v k)| ≤ a (k - j)) :
    ‖AbelCoboundary.average r v‖ ^ 2 ≤ D + 2 * A := by
  have hs := summable_geometric_of_diagonal r D hr0 hr1 hD v hdiag
  have ht := ((hs.hasSum.tendsto_sum_nat.const_smul (1 - r)).norm).pow 2
  apply le_of_tendsto ht
  exact Filter.Eventually.of_forall (fun N =>
    norm_finite_average_sq_le r D A hr0 hr1.le hD hA v a ha hdiag hprefix hoff N)

end RiemannResearch.Analysis.AbelGram
