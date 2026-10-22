/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ZeroOrdinateStopLoss
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Finite gap tails and interval-count moments

Finite algebra for unit-intensity circular gap statistics. The stop-loss and
shortfall duality are unconditional finite identities. The moment theorems are
finite probability results. A geometric application must separately establish
that the interval-count void probability equals `meanStopLoss`; no such geometric
claim is encoded as a theorem here.

Source: user-provided research argument; the Cantelli proof uses the elementary
nonnegative square `(s * X - (s ^ 2 + V)) ^ 2`. No novelty is claimed.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteGapVariance

open ZeroOrdinateStopLoss

variable {ι : Type*}

noncomputable def meanShortfall (S : Finset ι) (g : ι → ℝ) (L : ℝ) : ℝ :=
  (∑ i ∈ S, max (L - g i) 0) / (S.card : ℝ)

/-- Exact duality with the finite mean-gap term retained. -/
theorem meanShortfall_eq (S : Finset ι) (hS : S.Nonempty)
    (g : ι → ℝ) (L : ℝ) :
    meanShortfall S g L = L - meanGap S g + meanStopLoss S g L := by
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hS)
  have hpoint (i : ι) :
      max (L - g i) 0 = L - g i + max (g i - L) 0 := by
    by_cases h : g i ≤ L
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
      ring
    · have h' : L ≤ g i := le_of_lt (lt_of_not_ge h)
      rw [max_eq_right (sub_nonpos.mpr h'), max_eq_left (sub_nonneg.mpr h')]
      ring
  unfold meanShortfall meanStopLoss stopLossSum meanGap
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp [hcard]

/-- Lower-tail Markov bound, valid also for the empty finite family. -/
theorem small_tail_frequency_le_meanShortfall_div
    (S : Finset ι) (g : ι → ℝ) {y s : ℝ} (hys : y < s) :
    ((S.filter fun i => g i ≤ y).card : ℝ) / (S.card : ℝ) ≤
      meanShortfall S g s / (s-y) := by
  classical
  have hsum : (s-y) * ((S.filter fun i => g i ≤ y).card : ℝ) ≤
      ∑ i ∈ S, max (s-g i) 0 := by
    calc
      _ = ∑ i ∈ S.filter (fun i => g i ≤ y), (s-y) := by simp [mul_comm]; ring
      _ ≤ ∑ i ∈ S.filter (fun i => g i ≤ y), max (s-g i) 0 := by
        apply Finset.sum_le_sum
        intro i hi
        exact (sub_le_sub_left (Finset.mem_filter.mp hi).2 s).trans (le_max_left _ _)
      _ ≤ ∑ i ∈ S, max (s-g i) 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i hi hnot
        exact le_max_right _ _
  have hcard : ((S.filter fun i => g i ≤ y).card : ℝ) ≤
      (∑ i ∈ S, max (s-g i) 0) / (s-y) := by
    apply (le_div_iff₀ (sub_pos.mpr hys)).mpr
    simpa only [mul_comm] using hsum
  calc
    _ ≤ ((∑ i ∈ S, max (s-g i) 0) / (s-y)) / (S.card : ℝ) :=
      div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)
    _ = meanShortfall S g s / (s-y) := by
      unfold meanShortfall
      ring

section FiniteLaw

variable {α : Type*} [Fintype α]

noncomputable def zeroMass (w X : α → ℝ) : ℝ :=
  ∑ i, if X i = 0 then w i else 0

/-- The exact square identity underlying finite Cantelli. -/
theorem square_moment_identity (w X : α → ℝ) {s V : ℝ}
    (hmass : ∑ i, w i = 1) (hmean : ∑ i, w i * X i = s)
    (hsecond : ∑ i, w i * (X i) ^ 2 = s ^ 2 + V) :
    (∑ i, w i * (s * X i - (s ^ 2 + V)) ^ 2) = V * (s ^ 2 + V) := by
  calc
    _ = ∑ i, (s ^ 2 * (w i * (X i) ^ 2) -
        (2*s*(s ^ 2+V)) * (w i * X i) + (s ^ 2+V) ^ 2 * w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = s ^ 2 * (∑ i, w i * (X i) ^ 2) -
        (2*s*(s ^ 2+V)) * (∑ i, w i * X i) +
        (s ^ 2+V) ^ 2 * (∑ i, w i) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = V * (s ^ 2+V) := by rw [hmass, hmean, hsecond]; ring

/-- The zero-event Cantelli bound, derived from the first two moments. -/
theorem zeroMass_le_variance (w X : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) {s V : ℝ} (hs : 0 < s) (hV : 0 ≤ V)
    (hmass : ∑ i, w i = 1) (hmean : ∑ i, w i * X i = s)
    (hsecond : ∑ i, w i * (X i) ^ 2 = s ^ 2 + V) :
    zeroMass w X ≤ V / (s ^ 2 + V) := by
  classical
  have hq : 0 < s ^ 2 + V := by positivity
  have hsq : zeroMass w X * (s ^ 2+V) ^ 2 ≤
      ∑ i, w i * (s * X i - (s ^ 2+V)) ^ 2 := by
    unfold zeroMass
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hX : X i = 0
    · rw [if_pos hX, hX]
      ring_nf
      exact le_rfl
    · simp only [if_neg hX, zero_mul]
      exact mul_nonneg (hw i) (sq_nonneg _)
  rw [square_moment_identity w X hmass hmean hsecond] at hsq
  apply (le_div_iff₀ hq).mpr
  have hcancel : (zeroMass w X * (s ^ 2+V)) * (s ^ 2+V) ≤ V * (s ^ 2+V) := by
    nlinarith only [hsq]
  by_contra h
  have hpos := mul_pos (sub_pos.mpr (lt_of_not_ge h)) hq
  nlinarith only [hcancel, hpos]

/-- Exact integer identity retaining the higher-occupancy remainder. -/
theorem nat_factorial_excess_identity (k : ℕ) :
    (k : ℝ) * ((k : ℝ)-1) =
      2 * max ((k : ℝ)-1) 0 +
        max ((k : ℝ)-1) 0 * max ((k : ℝ)-2) 0 := by
  by_cases hk : k ≤ 1
  · have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl <;> norm_num
  · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    rw [max_eq_left (by linarith : 0 ≤ (k : ℝ)-1),
      max_eq_left (by linarith : 0 ≤ (k : ℝ)-2)]
    ring

/-- The positive excess is mean minus one plus the zero probability. -/
theorem excess_moment_identity (w : α → ℝ) (X : α → ℕ) {s : ℝ}
    (hmass : ∑ i, w i = 1) (hmean : ∑ i, w i * (X i : ℝ) = s) :
    (∑ i, w i * max ((X i : ℝ)-1) 0) =
      s - 1 + zeroMass w (fun i => (X i : ℝ)) := by
  classical
  have hpoint (i : α) :
      w i * max ((X i : ℝ)-1) 0 = w i * (X i : ℝ) - w i +
        (if (X i : ℝ) = 0 then w i else 0) := by
    by_cases hX : X i = 0
    · simp [hX]
    · have hX1 : (1 : ℝ) ≤ X i := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hX)
      have hXR : (X i : ℝ) ≠ 0 := by exact_mod_cast hX
      rw [max_eq_left (by linarith : 0 ≤ (X i : ℝ)-1), if_neg hXR]
      ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hmean, hmass]
  rfl

noncomputable def occupancyRemainder (w : α → ℝ) (X : α → ℕ) : ℝ :=
  ∑ i, w i * (max ((X i : ℝ)-1) 0 * max ((X i : ℝ)-2) 0)

theorem occupancyRemainder_nonneg (w : α → ℝ) (X : α → ℕ)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ occupancyRemainder w X := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i) (mul_nonneg (le_max_right _ _) (le_max_right _ _))

/-- Exact second-factorial-moment decomposition. -/
theorem factorial_moment_identity (w : α → ℝ) (X : α → ℕ) {s V : ℝ}
    (hmass : ∑ i, w i = 1) (hmean : ∑ i, w i * (X i : ℝ) = s)
    (hsecond : ∑ i, w i * (X i : ℝ) ^ 2 = s ^ 2 + V) :
    V + s ^ 2 - s = 2 * (s - 1 + zeroMass w (fun i => (X i : ℝ))) +
      occupancyRemainder w X := by
  have hfactor : (∑ i, w i * ((X i : ℝ) * ((X i : ℝ)-1))) = V+s ^ 2-s := by
    calc
      _ = ∑ i, (w i * (X i : ℝ) ^ 2 - w i * (X i : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = V+s ^ 2-s := by rw [Finset.sum_sub_distrib, hsecond, hmean]; ring
  rw [← hfactor]
  rw [← excess_moment_identity w X hmass hmean]
  simp_rw [nat_factorial_excess_identity]
  simp only [mul_add, Finset.sum_add_distrib]
  unfold occupancyRemainder
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Every central absolute moment controls the zero mass. -/
theorem zeroMass_mul_pow_le_centralMoment (w X : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) {s : ℝ} (hs : 0 ≤ s) (m : ℕ) :
    zeroMass w X * s ^ m ≤ ∑ i, w i * |X i-s| ^ m := by
  classical
  unfold zeroMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hX : X i = 0
  · simp [hX, abs_of_nonneg hs]
  · simp only [if_neg hX, zero_mul]
    exact mul_nonneg (hw i) (pow_nonneg (abs_nonneg _) _)

theorem zeroMass_le_centralMoment_div (w X : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) {s : ℝ} (hs : 0 < s) (m : ℕ) :
    zeroMass w X ≤ (∑ i, w i * |X i-s| ^ m) / s ^ m := by
  apply (le_div_iff₀ (pow_pos hs m)).mpr
  exact zeroMass_mul_pow_le_centralMoment w X hw (le_of_lt hs) m

/-- An integer-valued quadratic majorizes the zero indicator.
The two consecutive roots are essential: no integer lies strictly between them. -/
theorem nat_zero_indicator_le_quadratic (m k : ℕ) :
    (if (m : ℝ) = 0 then (k : ℝ) * ((k : ℝ) + 1) else 0) ≤
      ((m : ℝ) - (k : ℝ)) * ((m : ℝ) - (k : ℝ) - 1) := by
  by_cases hm : m = 0
  · subst m
    simp only [Nat.cast_zero, zero_sub]
    ring_nf
    exact le_rfl
  · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [if_neg hmR]
    by_cases hmk : m ≤ k
    · have hmkR : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have hkm : (k : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast (show k + 1 ≤ m by omega)
      exact mul_nonneg (by linarith) (by linarith)

/-- A discrete refinement of the variance bound for the zero mass.
It holds for every positive integer `k`; choosing adjacent roots around the
second-moment/first-moment ratio gives the optimal moment majorant. -/
theorem zeroMass_le_integer_moment_bound (w : α → ℝ) (X : α → ℕ)
    (hw : ∀ i, 0 ≤ w i) (k : ℕ) (hk : 1 ≤ k) {s V : ℝ}
    (hmass : ∑ i, w i = 1)
    (hmean : ∑ i, w i * (X i : ℝ) = s)
    (hsecond : ∑ i, w i * (X i : ℝ) ^ 2 = s ^ 2 + V) :
    zeroMass w (fun i => (X i : ℝ)) ≤
      (s ^ 2 + V - (2 * (k : ℝ) + 1) * s + (k : ℝ) * ((k : ℝ) + 1)) /
        ((k : ℝ) * ((k : ℝ) + 1)) := by
  classical
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hden : 0 < (k : ℝ) * ((k : ℝ) + 1) :=
    mul_pos hkpos (by linarith)
  have hpoly :
      (∑ i, w i * (((X i : ℝ) - (k : ℝ)) * ((X i : ℝ) - (k : ℝ) - 1))) =
        s ^ 2 + V - (2 * (k : ℝ) + 1) * s + (k : ℝ) * ((k : ℝ) + 1) := by
    calc
      _ = ∑ i, (w i * (X i : ℝ) ^ 2 -
          (2 * (k : ℝ) + 1) * (w i * (X i : ℝ)) +
          ((k : ℝ) * ((k : ℝ) + 1)) * w i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, w i * (X i : ℝ) ^ 2) -
          (2 * (k : ℝ) + 1) * (∑ i, w i * (X i : ℝ)) +
          ((k : ℝ) * ((k : ℝ) + 1)) * (∑ i, w i) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by rw [hsecond, hmean, hmass]; ring
  have hbound : zeroMass w (fun i => (X i : ℝ)) *
      ((k : ℝ) * ((k : ℝ) + 1)) ≤
      ∑ i, w i * (((X i : ℝ) - (k : ℝ)) * ((X i : ℝ) - (k : ℝ) - 1)) := by
    unfold zeroMass
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hpoint := mul_le_mul_of_nonneg_left
      (nat_zero_indicator_le_quadratic (X i) k) (hw i)
    by_cases hX : (X i : ℝ) = 0
    · simpa only [if_pos hX] using hpoint
    · simpa only [if_neg hX, mul_zero, zero_mul] using hpoint
  apply (le_div_iff₀ hden).mpr
  rw [hpoly] at hbound
  exact hbound

end FiniteLaw

section GapComposition

variable {α : Type*} [Fintype α]

/-- Finite large-gap consequence of the two count moments and the void identity. -/
theorem large_gap_tail_le_variance
    (S : Finset ι) (g : ι → ℝ) (w X : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) {s y V : ℝ} (hs : 0 < s) (hsy : s < y)
    (hV : 0 ≤ V) (hmass : ∑ i, w i = 1)
    (hmean : ∑ i, w i * X i = s)
    (hsecond : ∑ i, w i * (X i) ^ 2 = s ^ 2 + V)
    (hvoid : meanStopLoss S g s = zeroMass w X) :
    ((S.filter fun i => y ≤ g i).card : ℝ) / (S.card : ℝ) ≤
      V / ((s ^ 2+V) * (y-s)) := by
  classical
  have hcantelli := zeroMass_le_variance w X hw hs hV hmass hmean hsecond
  calc
    _ ≤ meanStopLoss S g s / (y-s) :=
      tail_frequency_le_meanStopLoss_div S g hsy
    _ ≤ (V / (s ^ 2+V)) / (y-s) := by
      rw [hvoid]
      exact div_le_div_of_nonneg_right hcantelli (le_of_lt (sub_pos.mpr hsy))
    _ = _ := by rw [div_div]

/-- Exact small-gap identity, retaining the higher-occupancy remainder. -/
theorem shortfall_factorial_identity
    (S : Finset ι) (hS : S.Nonempty) (g : ι → ℝ)
    (w : α → ℝ) (X : α → ℕ) {s V : ℝ}
    (hgap : meanGap S g = 1) (hmass : ∑ i, w i = 1)
    (hmean : ∑ i, w i * (X i : ℝ) = s)
    (hsecond : ∑ i, w i * (X i : ℝ) ^ 2 = s ^ 2 + V)
    (hvoid : meanStopLoss S g s = zeroMass w (fun i => (X i : ℝ))) :
    V+s ^ 2-s = 2 * meanShortfall S g s + occupancyRemainder w X := by
  rw [meanShortfall_eq S hS g s, hgap, hvoid]
  exact factorial_moment_identity w X hmass hmean hsecond

/-- The triangular-pair majorant for the finite gap shortfall. -/
theorem shortfall_le_second_factorial_moment
    (S : Finset ι) (hS : S.Nonempty) (g : ι → ℝ)
    (w : α → ℝ) (X : α → ℕ) (hw : ∀ i, 0 ≤ w i) {s V : ℝ}
    (hgap : meanGap S g = 1) (hmass : ∑ i, w i = 1)
    (hmean : ∑ i, w i * (X i : ℝ) = s)
    (hsecond : ∑ i, w i * (X i : ℝ) ^ 2 = s ^ 2 + V)
    (hvoid : meanStopLoss S g s = zeroMass w (fun i => (X i : ℝ))) :
    meanShortfall S g s ≤ (V+s ^ 2-s)/2 := by
  have hid := shortfall_factorial_identity S hS g w X hgap hmass hmean hsecond hvoid
  have hrem := occupancyRemainder_nonneg w X hw
  linarith

/-- Small-gap frequency bound obtained from the count's factorial moment. -/
theorem small_gap_tail_le_variance
    (S : Finset ι) (hS : S.Nonempty) (g : ι → ℝ)
    (w : α → ℝ) (X : α → ℕ) (hw : ∀ i, 0 ≤ w i) {s y V : ℝ}
    (hys : y < s) (hgap : meanGap S g = 1) (hmass : ∑ i, w i = 1)
    (hmean : ∑ i, w i * (X i : ℝ) = s)
    (hsecond : ∑ i, w i * (X i : ℝ) ^ 2 = s ^ 2 + V)
    (hvoid : meanStopLoss S g s = zeroMass w (fun i => (X i : ℝ))) :
    ((S.filter fun i => g i ≤ y).card : ℝ) / (S.card : ℝ) ≤
      (V+s ^ 2-s) / (2*(s-y)) := by
  classical
  have hshort := shortfall_le_second_factorial_moment S hS g w X hw
    hgap hmass hmean hsecond hvoid
  calc
    _ ≤ meanShortfall S g s / (s-y) :=
      small_tail_frequency_le_meanShortfall_div S g hys
    _ ≤ ((V+s ^ 2-s)/2) / (s-y) :=
      div_le_div_of_nonneg_right hshort (le_of_lt (sub_pos.mpr hys))
    _ = _ := by rw [div_div]

/-- Large-gap bound from an arbitrary central absolute moment of the count. -/
theorem large_gap_tail_le_centralMoment
    (S : Finset ι) (g : ι → ℝ) (w X : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) {s y : ℝ} (hs : 0 < s) (hsy : s < y) (m : ℕ)
    (hvoid : meanStopLoss S g s = zeroMass w X) :
    ((S.filter fun i => y ≤ g i).card : ℝ) / (S.card : ℝ) ≤
      (∑ i, w i * |X i-s| ^ m) / (s ^ m * (y-s)) := by
  classical
  calc
    _ ≤ meanStopLoss S g s / (y-s) :=
      tail_frequency_le_meanStopLoss_div S g hsy
    _ ≤ ((∑ i, w i * |X i-s| ^ m) / s ^ m) / (y-s) := by
      rw [hvoid]
      exact div_le_div_of_nonneg_right (zeroMass_le_centralMoment_div w X hw hs m)
        (le_of_lt (sub_pos.mpr hsy))
    _ = _ := by rw [div_div]

end GapComposition

end RiemannResearch.Analysis.FiniteGapVariance
