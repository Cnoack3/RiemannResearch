/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.WeakConvergenceDenseTests
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Escaping Riesz directions

Source: independently developed elementary Hilbert-space argument during
the October 19 triangular Gram investigation; no novelty claim is made.
A nonzero limiting pairing with a vanishing test forces norm escape.
Normalized representers with eventually fixed generator pairings then
converge weakly to zero. The RH consumer is QTriangularTargetDirection.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.Analysis
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
theorem norm_tendsto_atTop_of_vanishing_test_pairing (u v : ℕ → H)
    (hv : Tendsto (fun n => ‖v n‖) atTop (𝓝 0))
    (hp : Tendsto (fun n => inner ℝ (u n) (v n)) atTop (𝓝 1)) :
    Tendsto (fun n => ‖u n‖) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  let C : ℝ := max B 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; linarith [le_max_left B 0]
  have hsmall : ∀ᶠ n in atTop, ‖v n‖ < 1 / (2 * C) :=
    (tendsto_order.1 hv).2 _ (by positivity)
  have hsignal : ∀ᶠ n in atTop, (1 / 2 : ℝ) < inner ℝ (u n) (v n) :=
    (tendsto_order.1 hp).1 _ (by norm_num)
  filter_upwards [hsmall, hsignal] with n hn hp
  by_contra! hbad
  have hnorm : ‖u n‖ ≤ C := hbad.le.trans hBC
  have habs : |inner ℝ (u n) (v n)| ≤ ‖u n‖ * ‖v n‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (u n) (v n)
  have hproduct := mul_le_mul_of_nonneg_right hnorm (norm_nonneg (v n))
  have hsmall' := (lt_div_iff₀ (show 0 < 2 * C by positivity)).mp hn
  nlinarith [le_abs_self (inner ℝ (u n) (v n))]
theorem norm_normalize_le_one (u : H) : ‖‖u‖⁻¹ • u‖ ≤ 1 := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  by_cases hu : ‖u‖ = 0
  · simp [hu]
  · simp [inv_mul_cancel₀ hu]
theorem normalized_riesz_weak_zero [CompleteSpace H]
    (v : I → H) (u : ℕ → H)
    (hu : ∀ n, u n ∈ (Submodule.span ℝ (Set.range v)).topologicalClosure)
    (hescape : Tendsto (fun n => ‖u n‖) atTop atTop)
    (a : I → ℝ)
    (ha : ∀ i, ∀ᶠ n in atTop, inner ℝ (v i) (u n) = a i) (x : H) :
    Tendsto (fun n => inner ℝ x (‖u n‖⁻¹ • u n)) atTop (𝓝 0) := by
  let K := (Submodule.span ℝ (Set.range v)).topologicalClosure
  let z : ℕ → H := fun n => ‖u n‖⁻¹ • u n
  have hz : ∀ n, z n ∈ K := fun n => K.smul_mem _ (hu n)
  have ht : Tendsto (fun n => inner ℝ (K.starProjection x) (z n)) atTop (𝓝 0) := by
    apply tendsto_inner_zero_of_mem_closure_span (S := Set.range v) (C := 1)
      (by norm_num) (Eventually.of_forall (fun n => norm_normalize_le_one (u n)))
    · rintro y ⟨i, rfl⟩
      have hi := ((tendsto_inv_atTop_zero.comp hescape).mul_const (a i))
      simp only [zero_mul] at hi
      apply hi.congr'
      filter_upwards [ha i] with n hn
      simp only [Function.comp_apply, real_inner_smul_right, hn]
    · exact Submodule.starProjection_apply_mem K x
  have he (n : ℕ) : inner ℝ x (z n) = inner ℝ (K.starProjection x) (z n) := by
    have ho := Submodule.inner_right_of_mem_orthogonal (hz n)
      (Submodule.sub_starProjection_mem_orthogonal (K := K) x)
    rw [real_inner_comm (x - K.starProjection x) (z n), inner_sub_left] at ho
    linarith
  change Tendsto (fun n => inner ℝ x (z n)) atTop (𝓝 0)
  simpa only [he] using ht

end RiemannResearch.Analysis
