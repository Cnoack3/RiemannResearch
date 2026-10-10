import RiemannResearch.Analysis.RieszOrderUniformCoupling
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite midpoint refinements of all-order ordinate coupling

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

The predecessor RieszOrderUniformCoupling is left unchanged.

Mathlib API source is pinned to commit
51e6992efd06126df61a496bebf8f49482a4e129. In particular
Algebra/Order/BigOperators/Group/Finset.lean supplies the generated
sum_le_sum_of_subset_of_nonneg from its multiplicative theorem.

Every statement here is finite real algebra or exponential monotonicity.
The parameter restriction beta >= 1/2 is not an assertion of RH.
No zero location, zero separation, zero simplicity, or spectral integral
formula is assumed.

The split constants are 5, 89/18, 1111/225, ... . Their classical limit is
pi^2/2, but this file asserts only finite-order inequalities, not the
infinite-series identification. Wolfram was used only to check the rational
identities, not as a proof provider.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.TwistedRieszFilter

lemma reciprocal_square_midpoint_step {v : ℝ} (hv : (1 / 2 : ℝ) < v) :
    1 / v ^ 2 ≤ 1 / (v - 1 / 2) - 1 / (v + 1 / 2) := by
  have hl : 0 < v - 1 / 2 := by linarith
  have hr : 0 < v + 1 / 2 := by linarith
  have hid : 1 / (v - 1 / 2) - 1 / (v + 1 / 2) =
      1 / ((v - 1 / 2) * (v + 1 / 2)) := by
    rw [div_sub_div (1 : ℝ) (1 : ℝ) (ne_of_gt hl) (ne_of_gt hr)]
    have hnum : (1 : ℝ) * (v + 1 / 2) - (v - 1 / 2) * 1 = 1 := by ring
    rw [hnum]
  rw [hid]
  apply one_div_le_one_div_of_le (mul_pos hl hr)
  nlinarith

lemma reciprocalSquareSum_succ_eq (r : ℕ) (β : ℝ) :
    reciprocalSquareSum (r + 1) β = reciprocalSquareSum r β +
      1 / (β + ((r + 1 : ℕ) : ℝ)) ^ 2 := by
  unfold reciprocalSquareSum
  exact Finset.sum_range_succ (fun j : ℕ => 1 / (β + (j : ℝ)) ^ 2) (r + 1)

/-- Any finite prefix can be retained exactly. The endpoint is retained
also when the tail is empty, where the estimate is equality. -/
theorem reciprocalSquareSum_prefix_midpoint (m r : ℕ) {β : ℝ} (hβ : 0 < β) :
    reciprocalSquareSum (m + r) β ≤ reciprocalSquareSum m β +
      1 / (β + (m : ℝ) + 1 / 2) -
      1 / (β + ((m + r : ℕ) : ℝ) + 1 / 2) := by
  induction r with
  | zero =>
    simp only [Nat.add_zero]
    linarith
  | succ r ih =>
    have hn : 0 ≤ ((m + r : ℕ) : ℝ) := Nat.cast_nonneg _
    have hv : (1 / 2 : ℝ) < β + ((m + r : ℕ) : ℝ) + 1 := by linarith
    have hs : 1 / (β + ((m + r : ℕ) : ℝ) + 1) ^ 2 ≤
        1 / (β + ((m + r : ℕ) : ℝ) + 1 / 2) -
          1 / (β + ((m + r : ℕ) : ℝ) + 1 + 1 / 2) := by
      simpa only [show β + ((m + r : ℕ) : ℝ) + 1 - 1 / 2 =
        β + ((m + r : ℕ) : ℝ) + 1 / 2 by ring] using
          reciprocal_square_midpoint_step hv
    rw [Nat.add_succ, reciprocalSquareSum_succ_eq]
    simp only [Nat.cast_succ, ← add_assoc]
    calc
      reciprocalSquareSum (m + r) β +
          1 / (β + ((m + r : ℕ) : ℝ) + 1) ^ 2 ≤
          (reciprocalSquareSum m β + 1 / (β + (m : ℝ) + 1 / 2) -
            1 / (β + ((m + r : ℕ) : ℝ) + 1 / 2)) +
          (1 / (β + ((m + r : ℕ) : ℝ) + 1 / 2) -
            1 / (β + ((m + r : ℕ) : ℝ) + 1 + 1 / 2)) := add_le_add ih hs
      _ = reciprocalSquareSum m β + 1 / (β + (m : ℝ) + 1 / 2) -
            1 / (β + ((m + r : ℕ) : ℝ) + 1 + 1 / 2) := by ring

theorem reciprocalSquareSum_split_midpoint {m r : ℕ} (hmr : m ≤ r)
    {β : ℝ} (hβ : 0 < β) :
    reciprocalSquareSum r β ≤ reciprocalSquareSum m β +
      1 / (β + (m : ℝ) + 1 / 2) - 1 / (β + (r : ℝ) + 1 / 2) := by
  have he : m + (r - m) = r := by
    simpa only [Nat.add_comm] using Nat.sub_add_cancel hmr
  simpa only [he] using reciprocalSquareSum_prefix_midpoint m (r - m) hβ

/-- This sharpens the predecessor's coefficient beta^-2 + beta^-1.
The formula is valid for every r, including r=0. -/
theorem reciprocalSquareSum_midpoint (r : ℕ) {β : ℝ} (hβ : 0 < β) :
    reciprocalSquareSum r β ≤
      1 / β ^ 2 + 1 / (β + 1 / 2) - 1 / (β + (r : ℝ) + 1 / 2) := by
  simpa [reciprocalSquareSum] using reciprocalSquareSum_prefix_midpoint 0 r hβ

theorem reciprocalSquareSum_le_five_with_endpoint (r : ℕ) {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) :
    reciprocalSquareSum r β ≤ 5 - 1 / (β + (r : ℝ) + 1 / 2) := by
  have hb : 0 < β := by linarith
  have hfirst : 1 / β ^ 2 ≤ 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hb)).mpr
    nlinarith [sq_nonneg (β - 1 / 2)]
  have htail : 1 / (β + 1 / 2) ≤ 1 := by
    apply (div_le_iff₀ (by linarith : 0 < β + 1 / 2)).mpr
    linarith
  linarith [reciprocalSquareSum_midpoint r hb]

theorem reciprocalSquareSum_le_five (r : ℕ) {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) : reciprocalSquareSum r β ≤ 5 := by
  have he : 0 ≤ 1 / (β + (r : ℝ) + 1 / 2) := by positivity
  linarith [reciprocalSquareSum_le_five_with_endpoint r hβ]

lemma reciprocalSquareSum_mono_order {r m : ℕ} (hrm : r ≤ m) (β : ℝ) :
    reciprocalSquareSum r β ≤ reciprocalSquareSum m β := by
  unfold reciprocalSquareSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hrm 1))
  intro j _ _
  exact div_nonneg zero_le_one (sq_nonneg _)

lemma reciprocalSquareSum_le_at_half (m : ℕ) {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) :
    reciprocalSquareSum m β ≤ reciprocalSquareSum m (1 / 2) := by
  unfold reciprocalSquareSum
  apply Finset.sum_le_sum
  intro j _
  have hj : 0 < (1 / 2 : ℝ) + (j : ℝ) := by positivity
  apply one_div_le_one_div_of_le (sq_pos_of_pos hj)
  exact pow_le_pow_left₀ hj.le (by linarith) 2

/-- The first m+1 denominator terms are retained before midpoint comparison. -/
def midpointSplitConstant (m : ℕ) : ℝ :=
  reciprocalSquareSum m (1 / 2) + 1 / ((m : ℝ) + 1)

/-- A rational split coefficient retains the finite endpoint when its
chosen prefix is present. For three retained terms this requires r>=2. -/
theorem reciprocalSquareSum_midpointSplit_with_endpoint {m r : ℕ}
    (hmr : m ≤ r) {β : ℝ} (hβ : (1 / 2 : ℝ) ≤ β) :
    reciprocalSquareSum r β ≤ midpointSplitConstant m -
      1 / (β + (r : ℝ) + 1 / 2) := by
  have hp := reciprocalSquareSum_le_at_half m hβ
  have hs := reciprocalSquareSum_split_midpoint hmr (by linarith : 0 < β)
  have ht : 1 / (β + (m : ℝ) + 1 / 2) ≤ 1 / ((m : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity : 0 < (m : ℝ) + 1)
    linarith
  unfold midpointSplitConstant
  linarith

theorem reciprocalSquareSum_le_midpointSplit (m r : ℕ) {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) :
    reciprocalSquareSum r β ≤ midpointSplitConstant m := by
  have hb : 0 < β := by linarith
  have hp := reciprocalSquareSum_le_at_half m hβ
  unfold midpointSplitConstant
  by_cases hmr : m ≤ r
  · have hs := reciprocalSquareSum_split_midpoint hmr hb
    have he : 0 ≤ 1 / (β + (r : ℝ) + 1 / 2) := by positivity
    have ht : 1 / (β + (m : ℝ) + 1 / 2) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity : 0 < (m : ℝ) + 1)
      linarith
    linarith
  · have hrm : r ≤ m := Nat.le_of_lt (lt_of_not_ge hmr)
    have hs := reciprocalSquareSum_mono_order hrm β
    have ht : 0 ≤ 1 / ((m : ℝ) + 1) := by positivity
    linarith

lemma midpointSplitConstant_zero : midpointSplitConstant 0 = 5 := by
  norm_num [midpointSplitConstant, reciprocalSquareSum]

lemma midpointSplitConstant_one : midpointSplitConstant 1 = (89 / 18 : ℝ) := by
  norm_num [midpointSplitConstant, reciprocalSquareSum, Finset.sum_range_succ]

lemma midpointSplitConstant_two : midpointSplitConstant 2 = (1111 / 225 : ℝ) := by
  norm_num [midpointSplitConstant, reciprocalSquareSum, Finset.sum_range_succ]

/-- Each additional retained term strictly improves the uniform constant. -/
theorem midpointSplitConstant_step (m : ℕ) :
    midpointSplitConstant m - midpointSplitConstant (m + 1) =
      1 / (((m : ℝ) + 1) * ((m : ℝ) + 2) * (2 * (m : ℝ) + 3) ^ 2) := by
  have hdiff : midpointSplitConstant m - midpointSplitConstant (m + 1) =
      1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2) -
        1 / ((m : ℝ) + 1 + 1 / 2) ^ 2 := by
    unfold midpointSplitConstant
    rw [reciprocalSquareSum_succ_eq]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hdiff]
  have h1 : (m : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have h2 : (m : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
  have h3 : (m : ℝ) + 1 + 1 / 2 ≠ 0 := ne_of_gt (by positivity)
  have h4 : 2 * (m : ℝ) + 3 ≠ 0 := ne_of_gt (by positivity)
  field_simp [h1, h2, h3, h4]
  <;> ring

theorem midpointSplitConstant_strictly_decreases (m : ℕ) :
    midpointSplitConstant (m + 1) < midpointSplitConstant m := by
  have hp : 0 < 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2) *
      (2 * (m : ℝ) + 3) ^ 2) := by positivity
  linarith [midpointSplitConstant_step m]

/-- The uniform Gaussian coupling holds with every finite split constant. -/
theorem normalizedFrequencyKernel_uniform_midpoint_split (m r : ℕ) {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) (t : ℝ) :
    Real.exp (-(midpointSplitConstant m * t ^ 2)) ≤
      normalizedFrequencyKernel r β t := by
  have hs := reciprocalSquareSum_le_midpointSplit m r hβ
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg t)
  calc
    Real.exp (-(midpointSplitConstant m * t ^ 2)) ≤
        Real.exp (-(t ^ 2 * reciprocalSquareSum r β)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ normalizedFrequencyKernel r β t :=
      normalizedFrequencyKernel_gaussian_exact r β t

theorem normalizedFrequencyKernel_uniform_coupling_five (r : ℕ) {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) (t : ℝ) :
    Real.exp (-5 * t ^ 2) ≤ normalizedFrequencyKernel r β t := by
  simpa only [midpointSplitConstant_zero, neg_mul] using
    normalizedFrequencyKernel_uniform_midpoint_split 0 r hβ t

theorem normalizedFrequencyKernel_uniform_coupling_three_terms (r : ℕ) {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) (t : ℝ) :
    Real.exp (-(1111 / 225 : ℝ) * t ^ 2) ≤ normalizedFrequencyKernel r β t := by
  simpa only [midpointSplitConstant_two, neg_mul] using
    normalizedFrequencyKernel_uniform_midpoint_split 2 r hβ t

/-- The improved coupling is for the actual factorial-normalized rational
kernel, via the predecessor's exact positive-denominator factorization. -/
theorem spectralKernel_uniform_midpoint_split (m r : ℕ) {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) (t : ℝ) :
    Real.exp (-(midpointSplitConstant m * t ^ 2)) ≤
      spectralKernel r β t / spectralKernel r β 0 := by
  rw [spectralKernel_ratio r (by linarith : 0 < β) t]
  exact normalizedFrequencyKernel_uniform_midpoint_split m r hβ t

end RiemannResearch.Analysis.TwistedRieszFilter
