/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact innovation bounds for a geometric Gram kernel

Source: direct Gram--Schmidt and Bessel argument developed during the
24 September 2026 residual-dilation continuation. No novelty is claimed.
The RH consumer is `RH/ResidualGeometricInnovations`, which discharges the
Gram hypotheses for the actual Pareto dilation orbit. This module proves
finite and infinite energy bounds and the scalar identity used for the
geometric-scale square-summability estimate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis

section Generic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def geometricInnovation (t : ℕ → H) (q c : ℝ) : ℕ → H
  | 0 => t 0
  | j + 1 => c • (t (j + 1) - q • t j)

theorem geometricInnovation_orthonormal (t : ℕ → H) (q c : ℝ)
    (hgram : ∀ i j : ℕ, i ≤ j → inner ℝ (t i) (t j) = q ^ (j - i))
    (hc : c ^ 2 * (1 - q ^ 2) = 1) :
    Orthonormal ℝ (geometricInnovation t q c) := by
  have hself (i : ℕ) : inner ℝ (t i) (t i) = 1 := by
    simpa using hgram i i le_rfl
  have hstep (i : ℕ) : inner ℝ (t i) (t (i + 1)) = q := by
    simpa using hgram i (i + 1) (by omega)
  have hpast (i j : ℕ) (hij : i ≤ j) :
      inner ℝ (t i) (t (j + 1) - q • t j) = 0 := by
    rw [inner_sub_right, real_inner_smul_right,
      hgram i (j + 1) (by omega), hgram i j hij]
    have he : j + 1 - i = (j - i) + 1 := by omega
    rw [he, pow_succ]
    ring
  have hdiag (i : ℕ) :
      inner ℝ (t (i + 1) - q • t i) (t (i + 1) - q • t i) = 1 - q ^ 2 := by
    have hs : inner ℝ (t (i + 1)) (t i) = q := by
      rw [real_inner_comm]
      exact hstep i
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hself, hstep, hs]
    ring
  have hcross (i j : ℕ) (hij : i < j) :
      inner ℝ (t (i + 1) - q • t i) (t (j + 1) - q • t j) = 0 := by
    rw [inner_sub_left, real_inner_smul_left, hpast (i + 1) j (by omega),
      hpast i j (by omega)]
    ring
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | zero =>
    cases j with
    | zero => simpa [geometricInnovation] using hself 0
    | succ j =>
      simp only [geometricInnovation, real_inner_smul_right,
        hpast 0 j (Nat.zero_le j), mul_zero]
      simp
  | succ i =>
    cases j with
    | zero =>
      rw [real_inner_comm]
      simp only [geometricInnovation, real_inner_smul_right,
        hpast 0 i (Nat.zero_le i), mul_zero]
      simp
    | succ j =>
      simp only [geometricInnovation, real_inner_smul_left, real_inner_smul_right]
      by_cases hij : i = j
      · subst j
        rw [hdiag]
        simpa [pow_two, mul_assoc] using hc
      · have hz : inner ℝ (t (i + 1) - q • t i)
            (t (j + 1) - q • t j) = 0 := by
          rcases lt_or_gt_of_ne hij with h | h
          · exact hcross i j h
          · rw [real_inner_comm]
            exact hcross j i h
        simp [hz, hij]

theorem geometricInnovation_finite_bound (t : ℕ → H) (q c : ℝ)
    (hgram : ∀ i j : ℕ, i ≤ j → inner ℝ (t i) (t j) = q ^ (j - i))
    (hc : c ^ 2 * (1 - q ^ 2) = 1) (r : H) (N : ℕ) :
    (inner ℝ (t 0) r) ^ 2 + c ^ 2 *
      (∑ j ∈ Finset.range N,
        (inner ℝ (t (j + 1)) r - q * inner ℝ (t j) r) ^ 2) ≤ ‖r‖ ^ 2 := by
  have h := (geometricInnovation_orthonormal t q c hgram hc).sum_inner_products_le
    r (s := Finset.range (N + 1))
  simpa only [Finset.sum_range_succ', geometricInnovation,
    inner_sub_left, real_inner_smul_left, Real.norm_eq_abs, sq_abs, mul_pow,
    ← Finset.mul_sum, add_comm] using h


theorem geometricInnovation_weighted_summable (t : ℕ → H) (q c : ℝ)
    (hgram : ∀ i j : ℕ, i ≤ j → inner ℝ (t i) (t j) = q ^ (j - i))
    (hc : c ^ 2 * (1 - q ^ 2) = 1) (r : H) :
    Summable (fun j : ℕ => c ^ 2 *
      (inner ℝ (t (j + 1)) r - q * inner ℝ (t j) r) ^ 2) := by
  have hon := geometricInnovation_orthonormal t q c hgram hc
  have hs : Summable (fun j : ℕ => ‖inner ℝ (geometricInnovation t q c j) r‖ ^ 2) :=
    summable_of_sum_le (fun j => sq_nonneg _)
      (fun s => hon.sum_inner_products_le r (s := s))
  have hshift := hs.comp_injective Nat.succ_injective
  simpa only [Function.comp_def, geometricInnovation, inner_sub_left, real_inner_smul_left,
    Real.norm_eq_abs, sq_abs, mul_pow] using hshift

theorem geometricInnovation_infinite_bound (t : ℕ → H) (q c : ℝ)
    (hgram : ∀ i j : ℕ, i ≤ j → inner ℝ (t i) (t j) = q ^ (j - i))
    (hc : c ^ 2 * (1 - q ^ 2) = 1) (r : H) :
    (inner ℝ (t 0) r) ^ 2 +
      (∑' j : ℕ, c ^ 2 *
        (inner ℝ (t (j + 1)) r - q * inner ℝ (t j) r) ^ 2) ≤ ‖r‖ ^ 2 := by
  have hs := geometricInnovation_weighted_summable t q c hgram hc r
  have ht := (tendsto_const_nhds
    (x := (inner ℝ (t 0) r) ^ 2)).add hs.hasSum.tendsto_sum_nat
  apply le_of_tendsto' ht
  intro N
  simpa only [Finset.mul_sum] using geometricInnovation_finite_bound t q c hgram hc r N

end Generic

/-- Exact finite relation between AR(1/2) innovation energy and ordinary
first-difference energy, including both endpoint contributions. -/
theorem geometric_half_scalar_energy_identity (b : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), (b j) ^ 2) + (b 0) ^ 2 + (b N) ^ 2 +
      2 * (∑ j ∈ Finset.range N, (b (j + 1) - b j) ^ 2) =
    3 * (b 0) ^ 2 +
      4 * (∑ j ∈ Finset.range N, (b (j + 1) - (1 / 2 : ℝ) * b j) ^ 2) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    simp only [Finset.sum_range_succ] at ih ⊢
    nlinarith

end RiemannResearch.Analysis
