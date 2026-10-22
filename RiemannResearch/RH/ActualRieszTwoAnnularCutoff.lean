import RiemannResearch.RH.ActualRieszTwoConvolution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact finite arithmetic dilation of the annular Riesz filter

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

The finite sums retain every actual von Mangoldt prime-power coefficient.
Terms added when enlarging a cutoff have n>y and hence exact Riesz weight
zero. This proves the dilation identity without any asymptotic error.
The uncentered Riesz sum vanishes for every real x<=1; this provides the
boundary behavior needed by a subsequent Mellin dilation argument.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.ActualRieszTwo
open RiemannResearch.RH

/-- The actual uncentered sum is its own zero extension below 1. -/
theorem uncenteredRieszTwo_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) :
    uncenteredRieszTwo x = 0 := by
  have hf : ⌊x⌋₊ ≤ 1 := by
    simpa only [Nat.floor_one] using Nat.floor_mono hx
  unfold uncenteredRieszTwo
  apply Finset.sum_eq_zero
  intro n hn
  obtain ⟨hn1, hnf⟩ := Finset.mem_Icc.mp hn
  have he : n = 1 := le_antisymm (hnf.trans hf) hn1
  simp only [he, ArithmeticFunction.vonMangoldt_apply_one, zero_mul]

/-- A finite cutoff can be enlarged exactly, since every added weight is
zero, including the endpoint n=y. -/
theorem uncenteredRieszTwo_eq_fixed_cutoff {y X : ℝ}
    (hy : 0 < y) (hyX : y ≤ X) :
    uncenteredRieszTwo y =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        ArithmeticFunction.vonMangoldt n * rieszTwoWeight ((n : ℝ) / y) := by
  unfold uncenteredRieszTwo
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hn1, hnf⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨hn1, hnf.trans (Nat.floor_mono hyX)⟩
  · intro n hn hnnot
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnf : ⌊y⌋₊ < n := by
      by_contra h
      exact hnnot (Finset.mem_Icc.mpr ⟨hn1, le_of_not_gt h⟩)
    have hyn : y < (n : ℝ) := Nat.lt_of_floor_lt hnf
    have hratio : 1 ≤ (n : ℝ) / y :=
      (le_div_iff₀ hy).mpr (by simpa only [one_mul] using hyn.le)
    rw [rieszTwoWeight_of_one_le hratio]
    exact mul_zero _

/-- The actual finite annular sum is exactly the four dilated uncentered
Riesz sums. No prime correlation or spectral formula is assumed. -/
theorem uncenteredAnnular_eq_scaledRieszTwo {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt n * annularArithmeticWeight ((n : ℝ) / x)) =
      uncenteredRieszTwo x - (7 / 4 : ℝ) * uncenteredRieszTwo (x / 2) +
        (7 / 8 : ℝ) * uncenteredRieszTwo (x / 4) -
        (1 / 8 : ℝ) * uncenteredRieszTwo (x / 8) := by
  have hx2 : 0 < x / 2 := div_pos hx (by norm_num)
  have hx4 : 0 < x / 4 := div_pos hx (by norm_num)
  have hx8 : 0 < x / 8 := div_pos hx (by norm_num)
  have hx2le : x / 2 ≤ x := by linarith
  have hx4le : x / 4 ≤ x := by linarith
  have hx8le : x / 8 ≤ x := by linarith
  rw [uncenteredRieszTwo_eq_fixed_cutoff hx2 hx2le,
    uncenteredRieszTwo_eq_fixed_cutoff hx4 hx4le,
    uncenteredRieszTwo_eq_fixed_cutoff hx8 hx8le]
  unfold uncenteredRieszTwo
  have hscale (n : ℕ) (d : ℝ) : (n : ℝ) / (x / d) = d * ((n : ℝ) / x) := by
    rw [div_div_eq_mul_div]
    ring
  simp_rw [hscale]
  calc
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n * rieszTwoWeight ((n : ℝ) / x) -
          (7 / 4 : ℝ) *
            (ArithmeticFunction.vonMangoldt n * rieszTwoWeight (2 * ((n : ℝ) / x))) +
          (7 / 8 : ℝ) *
            (ArithmeticFunction.vonMangoldt n * rieszTwoWeight (4 * ((n : ℝ) / x))) -
          (1 / 8 : ℝ) *
            (ArithmeticFunction.vonMangoldt n * rieszTwoWeight (8 * ((n : ℝ) / x)))) := by
      apply Finset.sum_congr rfl
      intro n hn
      unfold annularArithmeticWeight
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

end RiemannResearch.RH.ActualRieszTwo
