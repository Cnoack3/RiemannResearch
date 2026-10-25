/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Removing directions orthogonal to the tested residual

Source: the user's shrinking-head and coupled-response handoff, 25 October 2026,
and the elementary orthogonal-projection refinement developed in its continuation.
These exact norm subtractions preserve the signed pairing. They do not provide
a uniform arithmetic bound.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.OrthogonalKernelScreening
open RiemannResearch.LinearAlgebra

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem rankOne_norm_sq (u v : E) (_hv : ‖v‖ ^ 2 ≠ 0) :
    ‖u - (inner ℝ u v / ‖v‖ ^ 2) • v‖ ^ 2 =
      ‖u‖ ^ 2 - (inner ℝ u v) ^ 2 / ‖v‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right]
  field_simp
  ring

theorem pairing_sq_le_rankOne (r u v : E) (hr : inner ℝ r v = 0)
    (hv : ‖v‖ ^ 2 ≠ 0) :
    (inner ℝ r u) ^ 2 ≤ ‖r‖ ^ 2 *
      (‖u‖ ^ 2 - (inner ℝ u v) ^ 2 / ‖v‖ ^ 2) := by
  have hp : inner ℝ r (u - (inner ℝ u v / ‖v‖ ^ 2) • v) = inner ℝ r u := by
    rw [inner_sub_right, real_inner_smul_right, hr, mul_zero, sub_zero]
  have h := abs_real_inner_le_norm r (u - (inner ℝ u v / ‖v‖ ^ 2) • v)
  have hh := mul_le_mul h h (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simpa only [← pow_two, sq_abs, mul_pow, hp, rankOne_norm_sq u v hv] using hh
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]
theorem pairing_sq_le_finite (r u : E) (z : ι → E) (c : ι → ℝ)
    (hr : ∀ i, inner ℝ r (z i) = 0)
    (hc : ∀ i, inner ℝ (z i) (finiteSchurCombination z c) = inner ℝ (z i) u) :
    (inner ℝ r u) ^ 2 ≤ ‖r‖ ^ 2 *
      (‖u‖ ^ 2 - ∑ i, c i * inner ℝ (z i) u) := by
  have hp : inner ℝ r (finiteSchurResidual u z c) = inner ℝ r u := by
    simp [finiteSchurResidual, finiteSchurCombination, inner_sub_right,
      inner_sum, real_inner_smul_right, hr]
  have h := abs_real_inner_le_norm r (finiteSchurResidual u z c)
  have hh := mul_le_mul h h (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simpa only [← pow_two, sq_abs, mul_pow, hp, finiteSchurResidual_norm_sq u z c hc] using hh
end
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]
theorem orthogonal_norm_sum (t : ι → E) (c : ι → ℝ)
    (ho : ∀ i j, i ≠ j → inner ℝ (t i) (t j) = 0) :
    ‖∑ i, c i • t i‖ ^ 2 = ∑ i, (c i) ^ 2 * ‖t i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq]; ring
  · intro j _ hji
    rw [ho j i hji]
    ring
  · simp

theorem weighted_bessel_finite (k : E) (t : ι → E) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ho : ∀ i j, i ≠ j → inner ℝ (t i) (t j) = 0)
    (ht : ∀ i, ‖t i‖ ^ 2 ≤ ρ * d i) :
    (∑ i, (inner ℝ k (t i)) ^ 2 / d i) ≤ ρ * ‖k‖ ^ 2 := by
  classical
  let c := fun i => inner ℝ k (t i) / d i
  let v := ∑ i, c i • t i
  let S := ∑ i, (inner ℝ k (t i)) ^ 2 / d i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (hd i).le)
  have hp : inner ℝ k v = S := by
    simp only [v, inner_sum, real_inner_smul_right, c, S]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hn : ‖v‖ ^ 2 ≤ ρ * S := by
    rw [show ‖v‖ ^ 2 = ∑ i, (c i) ^ 2 * ‖t i‖ ^ 2 from orthogonal_norm_sum t c ho]
    calc
      _ ≤ ∑ i, (c i) ^ 2 * (ρ * d i) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (ht i) (sq_nonneg _))
      _ = ρ * S := by
        dsimp [S]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [c]
        field_simp
  have hh := abs_real_inner_le_norm k v
  have hc : S ^ 2 ≤ ‖k‖ ^ 2 * ‖v‖ ^ 2 := by
    have hmul := mul_le_mul hh hh (abs_nonneg _) (by positivity)
    simpa only [← pow_two, sq_abs, mul_pow, hp] using hmul
  have hcs : S ^ 2 ≤ ‖k‖ ^ 2 * (ρ * S) :=
    hc.trans (mul_le_mul_of_nonneg_left hn (sq_nonneg _))
  change S ≤ ρ * ‖k‖ ^ 2
  by_cases hz : S = 0
  · rw [hz]; positivity
  · have hspos : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
    nlinarith
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*}
theorem weighted_bessel_complete (k : E) (t : ι → E) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ho : ∀ i j, i ≠ j → inner ℝ (t i) (t j) = 0)
    (ht : ∀ i, ‖t i‖ ^ 2 ≤ ρ * d i) :
    Summable (fun i => (inner ℝ k (t i)) ^ 2 / d i) ∧
      (∑' i, (inner ℝ k (t i)) ^ 2 / d i) ≤ ρ * ‖k‖ ^ 2 := by
  classical
  have hs (s : Finset ι) :
      (∑ i ∈ s, (inner ℝ k (t i)) ^ 2 / d i) ≤ ρ * ‖k‖ ^ 2 := by
    rw [← Finset.sum_coe_sort s (fun i => (inner ℝ k (t i)) ^ 2 / d i)]
    exact weighted_bessel_finite k (fun i : s => t i) (fun i : s => d i)
        (fun i => hd i) ρ hρ
        (fun i j hij => ho i j (fun h => hij (Subtype.ext h))) (fun i => ht i)
  have hn (i : ι) : 0 ≤ (inner ℝ k (t i)) ^ 2 / d i :=
    div_nonneg (sq_nonneg _) (hd i).le
  exact ⟨summable_of_sum_le hn hs, Real.tsum_le_of_sum_le hn hs⟩
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]
open RiemannResearch.LinearAlgebra
theorem orthogonal_normal (u : E) (z : ι → E)
    (hz : ∀ i, ‖z i‖ ^ 2 ≠ 0)
    (ho : ∀ i j, i ≠ j → inner ℝ (z i) (z j) = 0) (i : ι) :
    inner ℝ (z i) (finiteSchurCombination z
      (fun j => inner ℝ (z j) u / ‖z j‖ ^ 2)) = inner ℝ (z i) u := by
  classical
  simp only [finiteSchurCombination, inner_sum, real_inner_smul_right]
  rw [Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq, div_mul_cancel₀ _ (hz i)]
  · intro j _ hji
    rw [ho i j (Ne.symm hji), mul_zero]
  · simp

theorem orthogonal_screening_norm_sq (u : E) (z : ι → E)
    (hz : ∀ i, ‖z i‖ ^ 2 ≠ 0)
    (ho : ∀ i j, i ≠ j → inner ℝ (z i) (z j) = 0) :
    ‖finiteSchurResidual u z (fun i => inner ℝ (z i) u / ‖z i‖ ^ 2)‖ ^ 2 =
      ‖u‖ ^ 2 - ∑ i, (inner ℝ (z i) u) ^ 2 / ‖z i‖ ^ 2 := by
  rw [finiteSchurResidual_norm_sq _ _ _ (orthogonal_normal u z hz ho)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pairing_sq_le_orthogonal (r u : E) (z : ι → E)
    (hz : ∀ i, ‖z i‖ ^ 2 ≠ 0)
    (ho : ∀ i j, i ≠ j → inner ℝ (z i) (z j) = 0)
    (hr : ∀ i, inner ℝ r (z i) = 0) :
    (inner ℝ r u) ^ 2 ≤ ‖r‖ ^ 2 *
      (‖u‖ ^ 2 - ∑ i, (inner ℝ (z i) u) ^ 2 / ‖z i‖ ^ 2) := by
  have h := pairing_sq_le_finite r u z (fun i => inner ℝ (z i) u / ‖z i‖ ^ 2)
    hr (orthogonal_normal u z hz ho)
  have he : (∑ i, (inner ℝ (z i) u / ‖z i‖ ^ 2) * inner ℝ (z i) u) =
      ∑ i, (inner ℝ (z i) u) ^ 2 / ‖z i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rwa [he] at h
end
end RiemannResearch.Analysis.OrthogonalKernelScreening
