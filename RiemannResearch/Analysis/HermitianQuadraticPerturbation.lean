/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exact Hermitian quadratic perturbation

Source: Signed_Quadratic_Correction_Research_Note.pdf, §3.2.
The signed linear term is retained; only an operator-kernel hypothesis
removes it for arbitrary perturbations.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Fourier

def kernelMixed {ι : Type*} (s : Finset ι) (B : ι → ι → ℂ)
    (a h : ι → ℂ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s, star (a i) * B i j * h j

def kernelQuadratic {ι : Type*} (s : Finset ι) (B : ι → ι → ℂ)
    (a : ι → ℂ) : ℝ := (kernelMixed s B a a).re

theorem kernelMixed_swap {ι : Type*} (s : Finset ι) (B : ι → ι → ℂ)
    (a h : ι → ℂ) (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i) :
    kernelMixed s B a h = star (kernelMixed s B h a) := by
  unfold kernelMixed
  simp only [star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hB i hi j hj]
  ring

/-- Exact Hermitian perturbation identity, including the signed linear term. -/
theorem kernelQuadratic_perturbation {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a h : ι → ℂ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i) :
    kernelQuadratic s B (fun i => a i + h i) =
      kernelQuadratic s B a + 2 * (kernelMixed s B h a).re + kernelQuadratic s B h := by
  have hexpand : kernelMixed s B (fun i => a i + h i) (fun i => a i + h i) =
      kernelMixed s B a a + kernelMixed s B a h +
        kernelMixed s B h a + kernelMixed s B h h := by
    unfold kernelMixed
    simp only [star_add, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  unfold kernelQuadratic
  rw [hexpand, kernelMixed_swap s B a h hB]
  simp only [Complex.add_re]
  have hconj (z : ℂ) : (star z).re = z.re := rfl
  rw [hconj]
  ring

/-- An operator kernel, unlike a mere quadratic zero, kills the linear term. -/
theorem kernelQuadratic_perturbation_of_kernel {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a h : ι → ℂ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i)
    (ha : ∀ i ∈ s, ∑ j ∈ s, B i j * a j = 0) :
    kernelQuadratic s B (fun i => a i + h i) = kernelQuadratic s B h := by
  have hmixed (u : ι → ℂ) : kernelMixed s B u a = 0 := by
    unfold kernelMixed
    apply Finset.sum_eq_zero
    intro i hi
    calc
      (∑ j ∈ s, star (u i) * B i j * a j) =
          star (u i) * (∑ j ∈ s, B i j * a j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [ha i hi, mul_zero]
  rw [kernelQuadratic_perturbation s B a h hB]
  simp [kernelQuadratic, hmixed]

theorem kernelMixed_norm_le_action {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (h a : ι → ℂ) (δ : ι → ℝ)
    (ha : ∀ i ∈ s, ‖∑ j ∈ s, B i j * a j‖ ≤ δ i) :
    ‖kernelMixed s B h a‖ ≤ ∑ i ∈ s, ‖h i‖ * δ i := by
  have heq : kernelMixed s B h a =
      ∑ i ∈ s, star (h i) * (∑ j ∈ s, B i j * a j) := by
    unfold kernelMixed
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mul_sum, mul_assoc]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ s, ‖star (h i) * (∑ j ∈ s, B i j * a j)‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (ha i hi) (norm_nonneg _)

theorem kernelQuadratic_linear_remainder_bound {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a h : ι → ℂ) (δ : ι → ℝ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i)
    (ha : ∀ i ∈ s, ‖∑ j ∈ s, B i j * a j‖ ≤ δ i) :
    |kernelQuadratic s B (fun i => a i + h i) -
      kernelQuadratic s B a - kernelQuadratic s B h| ≤
      2 * ∑ i ∈ s, ‖h i‖ * δ i := by
  rw [kernelQuadratic_perturbation s B a h hB]
  have heq : kernelQuadratic s B a + 2 * (kernelMixed s B h a).re +
      kernelQuadratic s B h - kernelQuadratic s B a - kernelQuadratic s B h =
      2 * (kernelMixed s B h a).re := by ring
  rw [heq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left
    ((Complex.abs_re_le_norm _).trans (kernelMixed_norm_le_action s B h a δ ha))
    (by norm_num)

theorem kernelQuadratic_perturbation_abs_bound {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a h : ι → ℂ) (δ : ι → ℝ) (C : ℝ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i)
    (ha : ∀ i ∈ s, ‖∑ j ∈ s, B i j * a j‖ ≤ δ i)
    (hh : |kernelQuadratic s B h| ≤ C) :
    |kernelQuadratic s B (fun i => a i + h i) - kernelQuadratic s B a| ≤
      2 * ∑ i ∈ s, ‖h i‖ * δ i + C := by
  have hr := kernelQuadratic_linear_remainder_bound s B a h δ hB ha
  have ht := abs_add_le
    (kernelQuadratic s B (fun i => a i + h i) - kernelQuadratic s B a -
      kernelQuadratic s B h) (kernelQuadratic s B h)
  have heq : kernelQuadratic s B (fun i => a i + h i) - kernelQuadratic s B a -
      kernelQuadratic s B h + kernelQuadratic s B h =
      kernelQuadratic s B (fun i => a i + h i) - kernelQuadratic s B a := by ring
  rw [heq] at ht
  linarith

/-- Universal translation invariance characterizes the operator kernel exactly. -/
theorem kernelQuadratic_invariance_iff_kernel {ι : Type*} (s : Finset ι)
    (B : ι → ι → ℂ) (a : ι → ℂ)
    (hB : ∀ i ∈ s, ∀ j ∈ s, star (B i j) = B j i) :
    (∀ h : ι → ℂ, kernelQuadratic s B (fun i => a i + h i) =
      kernelQuadratic s B h) ↔
      ∀ i ∈ s, ∑ j ∈ s, B i j * a j = 0 := by
  constructor
  · intro hinv
    have hzero : kernelQuadratic s B a = 0 := by
      simpa [kernelQuadratic, kernelMixed] using hinv (fun _ => 0)
    let v : ι → ℂ := fun i => ∑ j ∈ s, B i j * a j
    have hmixed : (kernelMixed s B v a).re = ∑ i ∈ s, ‖v i‖ ^ 2 := by
      unfold kernelMixed
      have heq : (∑ i ∈ s, ∑ j ∈ s, star (v i) * B i j * a j) =
          ∑ i ∈ s, star (v i) * v i := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [v]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [heq, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
    have hvzero : ∑ i ∈ s, ‖v i‖ ^ 2 = 0 := by
      have heq := kernelQuadratic_perturbation s B a v hB
      rw [hinv v, hzero, hmixed] at heq
      linarith
    intro i hi
    have hvi : ‖v i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖v j‖)).mp hvzero i hi
    have hv : v i = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hvi)
    exact hv
  · intro ha h
    exact kernelQuadratic_perturbation_of_kernel s B a h hB ha

end RiemannResearch.Fourier
