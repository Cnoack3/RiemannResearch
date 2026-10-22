/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite weighted energy comparison with a controlled signed error

These elementary estimates compare the energy of a finite approximation
with that of its target once the energy of their difference is controlled.
For the damped Mobius consumer, that difference must first be formed using
the exact signed density-tail identity; the present inequalities do not
replace the tail by a sum of atomwise absolute errors.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis

/-- A weighted finite energy is bounded by twice the comparison energy
plus twice the energy of the signed difference. -/
theorem sum_weighted_sq_le_two_mul_add_sub_sq
    {ι : Type*} (s : Finset ι) (w f g : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * (f i) ^ 2) ≤
      2 * (∑ i ∈ s, w i * (g i) ^ 2) +
      2 * (∑ i ∈ s, w i * (f i - g i) ^ 2) := by
  calc
    (∑ i ∈ s, w i * (f i) ^ 2) ≤
        ∑ i ∈ s, (2 * (w i * (g i) ^ 2) +
          2 * (w i * (f i - g i) ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp : (f i) ^ 2 ≤ 2 * (g i) ^ 2 + 2 * (f i - g i) ^ 2 := by
        nlinarith [sq_nonneg (f i - 2 * g i)]
      have hm := mul_le_mul_of_nonneg_left hp (hw i hi)
      nlinarith
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- A uniform bound on the energy of the signed error gives energy
comparison in both directions, with the same explicit additive constant. -/
theorem sum_weighted_sq_comparison_of_sub_sq_le
    {ι : Type*} (s : Finset ι) (w f g : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (K : ℝ)
    (herror : (∑ i ∈ s, w i * (f i - g i) ^ 2) ≤ K) :
    ((∑ i ∈ s, w i * (f i) ^ 2) ≤
      2 * (∑ i ∈ s, w i * (g i) ^ 2) + 2 * K) ∧
    ((∑ i ∈ s, w i * (g i) ^ 2) ≤
      2 * (∑ i ∈ s, w i * (f i) ^ 2) + 2 * K) := by
  have hfg := sum_weighted_sq_le_two_mul_add_sub_sq s w f g hw
  have hgf := sum_weighted_sq_le_two_mul_add_sub_sq s w g f hw
  have heq : (∑ i ∈ s, w i * (g i - f i) ^ 2) =
      ∑ i ∈ s, w i * (f i - g i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq] at hgf
  exact ⟨by linarith, by linarith⟩


/-- Weighted Cauchy--Schwarz, retaining the signs of both factors. -/
theorem sum_weighted_mul_sq_le {ι : Type*} (s : Finset ι) (w f g : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i * g i)^2 ≤
      (∑ i ∈ s, w i * (f i)^2) * (∑ i ∈ s, w i * (g i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (w i) * f i) (fun i => Real.sqrt (w i) * g i)
  have hp (a : ι → ℝ) :
      (∑ i ∈ s, (Real.sqrt (w i) * a i)^2) = ∑ i ∈ s, w i * (a i)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have hm : (∑ i ∈ s, (Real.sqrt (w i) * f i) * (Real.sqrt (w i) * g i)) =
      ∑ i ∈ s, w i * f i * g i := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = (Real.sqrt (w i))^2 * f i * g i := by ring
      _ = _ := by rw [Real.sq_sqrt (hw i hi)]
  simpa only [hp, hm] using h

/-- Vanishing weighted square error transfers finite energies on moving
finite sets. Only a uniform bound on the target energy is needed. -/
theorem sum_weighted_sq_sub_tendsto_zero {ι : Type*}
    (s : ℕ → Finset ι) (w : ι → ℝ) (f : ℕ → ι → ℝ) (g : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (E : ℝ)
    (hE : ∀ j, (∑ i ∈ s j, w i * (g i)^2) ≤ E)
    (herr : Filter.Tendsto (fun j => ∑ i ∈ s j, w i * (f j i - g i)^2)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun j =>
      (∑ i ∈ s j, w i * (f j i)^2) - (∑ i ∈ s j, w i * (g i)^2))
      Filter.atTop (nhds 0) := by
  let e := fun j => ∑ i ∈ s j, w i * (f j i - g i)^2
  have he (j) : 0 ≤ e j := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have ht : Filter.Tendsto (fun j => 2 * Real.sqrt (E * e j) + e j)
      Filter.atTop (nhds 0) := by
    have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp
      (Filter.Tendsto.const_mul E herr)
    simpa using (hroot.const_mul 2).add herr
  apply squeeze_zero_norm _ ht
  intro j
  let c := ∑ i ∈ s j, w i * g i * (f j i - g i)
  have hc : c^2 ≤ E * e j :=
    (sum_weighted_mul_sq_le (s j) w g (fun i => f j i - g i)
      (fun i _ => hw i)).trans (mul_le_mul_of_nonneg_right (hE j) (he j))
  have hca : |c| ≤ Real.sqrt (E * e j) := by
    simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hc
  have hid : (∑ i ∈ s j, w i * (f j i)^2) - (∑ i ∈ s j, w i * (g i)^2) =
      2 * c + e j := by
    dsimp [c, e]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [Real.norm_eq_abs, hid]
  calc
    |2 * c + e j| ≤ |2 * c| + |e j| := abs_add_le _ _
    _ = 2 * |c| + e j := by rw [abs_mul, abs_of_nonneg (he j)]; norm_num
    _ ≤ _ := by linarith

end RiemannResearch.Analysis
