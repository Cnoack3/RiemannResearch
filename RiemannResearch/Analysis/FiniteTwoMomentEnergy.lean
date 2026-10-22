/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact two-moment finite energy

An orthogonal two-vector projection identity, retaining the squared remainder.
Concrete consumer: the repeated boundary root model in
`RiemannResearch.RH.BurnolDoubleRootModel`.
Source for the projection strategy: J.-F. Burnol, arXiv:math/0103058v2,
Section 2. The finite scalar proof here is elementary; no novelty is claimed.
-/
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteTwoMomentEnergy

/-- Exact Pythagorean decomposition for two orthogonal finite vectors. -/
theorem two_moment_decomposition {ι : Type*} (s : Finset ι)
    (x r : ι → ℝ) (m v a b : ℝ)
    (hm : m ≠ 0) (hv : v ≠ 0)
    (hcard : (s.card : ℝ) = m)
    (hx : ∑ j ∈ s, x j = 0)
    (hxx : ∑ j ∈ s, (x j) ^ 2 = v)
    (hr : ∑ j ∈ s, r j = a)
    (hxr : ∑ j ∈ s, x j * r j = b) :
    (∑ j ∈ s, (r j) ^ 2) = a ^ 2 / m + b ^ 2 / v +
      ∑ j ∈ s, (r j - a / m - (b / v) * x j) ^ 2 := by
  have hp (j : ι) : (r j - a / m - (b / v) * x j) ^ 2 =
      (r j) ^ 2 - (2 * a / m) * r j - (2 * b / v) * (x j * r j) +
      (a / m) ^ 2 + (2 * (a / m) * (b / v)) * x j +
      (b / v) ^ 2 * (x j) ^ 2 := by ring
  have hs : (∑ j ∈ s, (r j - a / m - (b / v) * x j) ^ 2) =
      (∑ j ∈ s, (r j) ^ 2) - (2 * a / m) * a - (2 * b / v) * b +
      m * (a / m) ^ 2 + (b / v) ^ 2 * v := by
    simp_rw [hp]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    rw [hcard, hx, hxx, hr, hxr]
    ring
  rw [hs]
  field_simp [hm, hv]
  <;> ring

/-- The two moment constraints give a sharp lower bound. -/
theorem two_moment_lower_bound {ι : Type*} (s : Finset ι)
    (x r : ι → ℝ) (m v a b : ℝ)
    (hm : m ≠ 0) (hv : v ≠ 0)
    (hcard : (s.card : ℝ) = m)
    (hx : ∑ j ∈ s, x j = 0)
    (hxx : ∑ j ∈ s, (x j) ^ 2 = v)
    (hr : ∑ j ∈ s, r j = a)
    (hxr : ∑ j ∈ s, x j * r j = b) :
    a ^ 2 / m + b ^ 2 / v ≤ ∑ j ∈ s, (r j) ^ 2 := by
  rw [two_moment_decomposition s x r m v a b hm hv hcard hx hxx hr hxr]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The affine vector attains both moment constraints and the lower bound. -/
theorem two_moment_attainment {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (m v a b : ℝ)
    (hm : m ≠ 0) (hv : v ≠ 0)
    (hcard : (s.card : ℝ) = m)
    (hx : ∑ j ∈ s, x j = 0)
    (hxx : ∑ j ∈ s, (x j) ^ 2 = v) :
    (∑ j ∈ s, (a / m + (b / v) * x j)) = a ∧
    (∑ j ∈ s, x j * (a / m + (b / v) * x j)) = b ∧
    (∑ j ∈ s, (a / m + (b / v) * x j) ^ 2) = a ^ 2 / m + b ^ 2 / v := by
  have ha : (∑ j ∈ s, (a / m + (b / v) * x j)) = a := by
    simp only [Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum]
    rw [hcard, hx]
    field_simp [hm, hv]
    <;> ring
  have hb : (∑ j ∈ s, x j * (a / m + (b / v) * x j)) = b := by
    have hp (j : ι) : x j * (a / m + (b / v) * x j) =
        (a / m) * x j + (b / v) * (x j) ^ 2 := by ring
    simp_rw [hp]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx, hxx]
    field_simp [hm, hv]
    <;> ring
  refine ⟨ha, hb, ?_⟩
  rw [two_moment_decomposition s x (fun j => a / m + (b / v) * x j)
    m v a b hm hv hcard hx hxx ha hb]
  have hz : (∑ j ∈ s,
      ((a / m + (b / v) * x j) - a / m - (b / v) * x j) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    ring
  rw [hz, add_zero]

end RiemannResearch.Analysis.FiniteTwoMomentEnergy
