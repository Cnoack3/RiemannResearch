/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

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

end RiemannResearch.Fourier
