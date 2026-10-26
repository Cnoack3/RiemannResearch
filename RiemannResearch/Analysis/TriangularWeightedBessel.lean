/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.OrthogonalKernelScreening
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Layered weighted Bessel estimates

Source: elementary orthogonal-family and finite-layer summation developed
in continuation of the user's odd-radical projection handoff, 25 October 2026.

For an orthogonal family of vectors of norm at most one, a nonnegative
combination of Bessel inequalities on nested support layers survives
orthogonalization. The support condition is encoded by exact pairing
identities, so the statement applies to arbitrary Hilbert-space tails.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.TriangularWeightedBessel
open RiemannResearch.Analysis.OrthogonalKernelScreening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Sum Bessel bounds over finitely many support layers. No completeness of
the orthogonal family, and no invertible Gram matrix, is required. -/
theorem layered_bessel
    (f : E) (u : ι → E) (v : κ → E)
    (selected : κ → ι → Prop) [∀ k i, Decidable (selected k i)]
    (δ : κ → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (ho : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0)
    (hn : ∀ i, ‖u i‖ ^ 2 ≤ 1)
    (hp : ∀ k i, selected k i → inner ℝ (v k) (u i) = inner ℝ f (u i)) :
    (∑ i, (∑ k, if selected k i then δ k else 0) *
      (inner ℝ f (u i)) ^ 2) ≤ ∑ k, δ k * ‖v k‖ ^ 2 := by
  classical
  have hb (k : κ) :
      (∑ i, if selected k i then (inner ℝ f (u i)) ^ 2 else 0) ≤
        ‖v k‖ ^ 2 := by
    have h := weighted_bessel_finite (v k)
      (fun i => if selected k i then u i else 0) (fun _ => (1 : ℝ))
      (fun _ => by norm_num) 1 (by norm_num)
      (by
        intro i j hij
        by_cases hi : selected k i <;> by_cases hj : selected k j
        · simpa only [if_pos hi, if_pos hj] using ho i j hij
        · simp [hi, hj]
        · simp [hi, hj]
        · simp [hi, hj])
      (by
        intro i
        by_cases hi : selected k i
        · simpa [hi] using hn i
        · simp [hi])
    have he (i : ι) :
        (inner ℝ (v k) (if selected k i then u i else 0)) ^ 2 / 1 =
          if selected k i then (inner ℝ f (u i)) ^ 2 else 0 := by
      by_cases hi : selected k i
      · simp [hi, hp k i hi]
      · simp [hi]
    simpa only [he, one_mul] using h
  calc
    _ = ∑ k, δ k *
        (∑ i, if selected k i then (inner ℝ f (u i)) ^ 2 else 0) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : selected k i <;> simp [hi]
    _ ≤ _ := Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_left (hb k) (hδ k))

private theorem screened_layer_norm_sq (v w : E) :
    ‖v - (inner ℝ v w / ‖w‖ ^ 2) • w‖ ^ 2 =
      ‖v‖ ^ 2 - (inner ℝ v w) ^ 2 / ‖w‖ ^ 2 := by
  by_cases hw : w = 0
  · simp [hw]
  · exact rankOne_norm_sq v w (pow_ne_zero _ (norm_ne_zero_iff.mpr hw))

/-- Rank-one layer subtraction followed by Bessel. Screening vectors may vanish. -/
theorem layered_screened_bessel
    (f : E) (u : ι → E) (v w : κ → E)
    (selected : κ → ι → Prop) [∀ k i, Decidable (selected k i)]
    (δ : κ → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (ho : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0)
    (hn : ∀ i, ‖u i‖ ^ 2 ≤ 1)
    (hp : ∀ k i, selected k i → inner ℝ (v k) (u i) = inner ℝ f (u i))
    (hw : ∀ k i, selected k i → inner ℝ (w k) (u i) = 0) :
    (∑ i, (∑ k, if selected k i then δ k else 0) *
      (inner ℝ f (u i)) ^ 2) +
      (∑ k, δ k * (inner ℝ (v k) (w k)) ^ 2 / ‖w k‖ ^ 2) ≤
        ∑ k, δ k * ‖v k‖ ^ 2 := by
  have h := layered_bessel f u
    (fun k => v k - (inner ℝ (v k) (w k) / ‖w k‖ ^ 2) • w k)
    selected δ hδ ho hn (by
      intro k i hki
      rw [inner_sub_left, real_inner_smul_left, hw k i hki, mul_zero, sub_zero]
      exact hp k i hki)
  simp_rw [screened_layer_norm_sq, mul_sub, Finset.sum_sub_distrib] at h
  have he : (∑ k, δ k * ((inner ℝ (v k) (w k)) ^ 2 / ‖w k‖ ^ 2)) =
      ∑ k, δ k * (inner ℝ (v k) (w k)) ^ 2 / ‖w k‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at h
  linarith
end RiemannResearch.Analysis.TriangularWeightedBessel
