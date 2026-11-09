/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.BoundedWeakInterpolation
import Mathlib.Tactic.Linarith

/-!
# Bounded lifting of a convergent operator image

Source: Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf,
Theorem 8.1 and Section 8.2. This is the standard weak compactness argument.
The norm bound is an explicit hypothesis; no compactness of the operator is needed.

The source norm bound remains explicit in every declaration.
-/

noncomputable section
open Filter
open scoped Topology

namespace Submodule

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- A convergent image of a bounded sequence has a preimage in the same closed
source subspace and norm ball. This uses weak compactness of the source ball. -/
theorem exists_mem_of_bounded_image_tendsto (S : Submodule ℝ H)
    [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T : H →L[ℝ] K) (C : ℝ) (F : ℕ → H) (y : K)
    (hmem : ∀ n, F n ∈ S) (hbound : ∀ n, ‖F n‖ ≤ C)
    (hlim : Tendsto (fun n => T (F n)) atTop (𝓝 y)) :
    ∃ f ∈ S, ‖f‖ ≤ C ∧ T f = y := by
  obtain ⟨f, hf, hn, ht⟩ := S.exists_mem_of_bounded_test_limits C F hmem hbound
    (fun z : K => (innerSL ℝ z).comp T) (fun z : K => inner ℝ z y)
    (fun z => ((innerSL ℝ z).continuous.tendsto y).comp hlim)
  refine ⟨f, hf, hn, ?_⟩
  have he := ht (T f - y)
  change inner ℝ (T f - y) (T f) = inner ℝ (T f - y) y at he
  have hz : inner ℝ (T f - y) (T f - y) = 0 := by
    rw [inner_sub_right, he, sub_self]
  rw [real_inner_self_eq_norm_sq] at hz
  apply sub_eq_zero.mp
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (T f - y)])

/-- Injectivity identifies the bounded weak lift with the prescribed target. -/
theorem mem_of_bounded_injective_image_tendsto (S : Submodule ℝ H)
    [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T : H →L[ℝ] K) (hT : Function.Injective T)
    (C : ℝ) (F : ℕ → H) (x : H)
    (hmem : ∀ n, F n ∈ S) (hbound : ∀ n, ‖F n‖ ≤ C)
    (hlim : Tendsto (fun n => T (F n)) atTop (𝓝 (T x))) :
    x ∈ S ∧ ‖x‖ ≤ C := by
  obtain ⟨f, hf, hn, he⟩ :=
    S.exists_mem_of_bounded_image_tendsto T C F (T x) hmem hbound hlim
  have hfx : f = x := hT he
  exact hfx ▸ ⟨hf, hn⟩

/-- Only a bounded cofinal subsequence is required. -/
theorem mem_of_bounded_subsequence_injective_image_tendsto (S : Submodule ℝ H)
    [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T : H →L[ℝ] K) (hT : Function.Injective T)
    (C : ℝ) (F : ℕ → H) (x : H) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop)
    (hmem : ∀ n, F n ∈ S) (hbound : ∀ n, ‖F (φ n)‖ ≤ C)
    (hlim : Tendsto (fun n => T (F n)) atTop (𝓝 (T x))) :
    x ∈ S ∧ ‖x‖ ≤ C :=
  S.mem_of_bounded_injective_image_tendsto T hT C (F ∘ φ) x
    (fun n => hmem (φ n)) hbound (hlim.comp hφ)

end Submodule
