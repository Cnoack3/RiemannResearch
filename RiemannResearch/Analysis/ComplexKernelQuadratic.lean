/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.Analysis.CompactKernelQuadraticContinuity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Real-to-complex quadratic transfer for symmetric real kernels
Source: user-provided task, supports the decomposition and transfer statement.
The form below is the actual conjugate-first, unnormalized complex iterated
integral. Compact support and kernel continuity establish absolute product
integrability; symmetry cancels the two imaginary cross terms by product swap.
The algebraic decomposition needs neither mean zero nor square integrability.
Those requirements are retained explicitly in the conditional positivity theorem.
This module asserts no arithmetic positivity, completed-Weil identification,
gauge change, or RH consequence.
-/

open scoped ComplexConjugate
open MeasureTheory Set Filter
namespace RiemannResearch.Analysis

/-- Actual conjugate-first complex quadratic integral for a real kernel. -/
noncomputable def complexKernelQuadratic (k : ℝ → ℝ → ℝ) (u : ℝ → ℂ) : ℂ :=
  ∫ x, conj (u x) * (∫ y, (k x y : ℂ) * u y)

/-- Joint continuity gives absolute integrability of each real cross-product
on a common compact support window, including the zero-radius window. -/
theorem integrable_realKernel_product_of_continuous
    {k : ℝ → ℝ → ℝ} {f g : ℝ → ℝ} {R : ℝ}
    (hk : Continuous (Function.uncurry k))
    (hf : Integrable f) (hg : Integrable g)
    (hfs : ∀ x ∉ Icc (-R) R, f x = 0)
    (hgs : ∀ x ∉ Icc (-R) R, g x = 0) :
    Integrable (fun p : ℝ × ℝ => f p.1 * k p.1 p.2 * g p.2)
      (volume.prod volume) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (-R) R ×ˢ Icc (-R) R) hk.continuousOn
  apply integrable_realKernel_product measurableSet_Icc (le_max_right C 0)
    hk.measurable _ hf hg hfs hgs
  intro x hx y hy
  exact (hC (x,y) ⟨hx,hy⟩).trans (le_max_left _ _)

private theorem complexKernel_product_decomposition
    (k : ℝ → ℝ → ℝ) (u : ℝ → ℂ) (p : ℝ × ℝ) :
    conj (u p.1) * (k p.1 p.2 : ℂ) * u p.2 =
      ((u p.1).re * k p.1 p.2 * (u p.2).re +
        (u p.1).im * k p.1 p.2 * (u p.2).im : ℝ) +
      (((u p.1).re * k p.1 p.2 * (u p.2).im -
        (u p.1).im * k p.1 p.2 * (u p.2).re : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

/-- Absolute product integrability of the actual conjugate-first integrand. -/
theorem integrable_complexKernel_product
    {k : ℝ → ℝ → ℝ} {u : ℝ → ℂ} {R : ℝ}
    (hk : Continuous (Function.uncurry k)) (hu : Integrable u)
    (hus : ∀ x ∉ Icc (-R) R, u x = 0) :
    Integrable (fun p : ℝ × ℝ => conj (u p.1) * (k p.1 p.2 : ℂ) * u p.2)
      (volume.prod volume) := by
  have hrs : ∀ x ∉ Icc (-R) R, (u x).re = 0 := by
    intro x hx; simp [hus x hx]
  have his : ∀ x ∉ Icc (-R) R, (u x).im = 0 := by
    intro x hx; simp [hus x hx]
  have hur : Integrable (fun x => (u x).re) := hu.re
  have hui : Integrable (fun x => (u x).im) := hu.im
  have hrr := integrable_realKernel_product_of_continuous hk hur hur hrs hrs
  have hii := integrable_realKernel_product_of_continuous hk hui hui his his
  have hri := integrable_realKernel_product_of_continuous hk hur hui hrs his
  have hir := integrable_realKernel_product_of_continuous hk hui hur his hrs
  have hA : Integrable (fun p : ℝ × ℝ =>
      (((u p.1).re * k p.1 p.2 * (u p.2).re +
        (u p.1).im * k p.1 p.2 * (u p.2).im : ℝ) : ℂ))
      (volume.prod volume) := (hrr.add hii).ofReal
  have hB : Integrable (fun p : ℝ × ℝ =>
      (((u p.1).re * k p.1 p.2 * (u p.2).im -
        (u p.1).im * k p.1 p.2 * (u p.2).re : ℝ) : ℂ) * Complex.I)
      (volume.prod volume) := (hri.sub hir).ofReal.mul_const Complex.I
  simp_rw [complexKernel_product_decomposition]
  exact hA.add hB

/-- Fubini for the actual complex form, with an explicit integrability hypothesis. -/
theorem complexKernelQuadratic_eq_product
    {k : ℝ → ℝ → ℝ} {u : ℝ → ℂ}
    (h : Integrable (fun p : ℝ × ℝ => conj (u p.1) * (k p.1 p.2 : ℂ) * u p.2)
      (volume.prod volume)) :
    complexKernelQuadratic k u =
      ∫ p : ℝ × ℝ, conj (u p.1) * (k p.1 p.2 : ℂ) * u p.2 ∂volume.prod volume := by
  rw [integral_prod _ h]
  simp only [complexKernelQuadratic, mul_assoc, integral_const_mul]

/-- The outer integrand is integrable; thus the form is not using the default
value of a nonintegrable Bochner integral. -/
theorem integrable_complexKernel_outer
    {k : ℝ → ℝ → ℝ} {u : ℝ → ℂ} {R : ℝ}
    (hk : Continuous (Function.uncurry k)) (hu : Integrable u)
    (hus : ∀ x ∉ Icc (-R) R, u x = 0) :
    Integrable (fun x => conj (u x) * (∫ y, (k x y : ℂ) * u y)) := by
  simpa only [mul_assoc, integral_const_mul] using
    (integrable_complexKernel_product hk hu hus).integral_prod_left

/-- A real symmetric kernel gives exactly the sum of the real and imaginary
real quadratic forms. Symmetry removes the cross term without a sign or
normalization change. -/
theorem complexKernelQuadratic_eq_realKernelQuadratic_re_add_im
    {k : ℝ → ℝ → ℝ} {u : ℝ → ℂ} {R : ℝ}
    (hk : Continuous (Function.uncurry k))
    (hsymm : ∀ x y, k x y = k y x)
    (hu : Integrable u) (hus : ∀ x ∉ Icc (-R) R, u x = 0) :
    complexKernelQuadratic k u =
      ((realKernelQuadratic k (fun x => (u x).re) +
        realKernelQuadratic k (fun x => (u x).im) : ℝ) : ℂ) := by
  have hrs : ∀ x ∉ Icc (-R) R, (u x).re = 0 := by
    intro x hx; simp [hus x hx]
  have his : ∀ x ∉ Icc (-R) R, (u x).im = 0 := by
    intro x hx; simp [hus x hx]
  have hur : Integrable (fun x => (u x).re) := hu.re
  have hui : Integrable (fun x => (u x).im) := hu.im
  have hrr := integrable_realKernel_product_of_continuous hk hur hur hrs hrs
  have hii := integrable_realKernel_product_of_continuous hk hui hui his his
  have hri := integrable_realKernel_product_of_continuous hk hur hui hrs his
  have hir := integrable_realKernel_product_of_continuous hk hui hur his hrs
  have hA : Integrable (fun p : ℝ × ℝ =>
      (((u p.1).re * k p.1 p.2 * (u p.2).re +
        (u p.1).im * k p.1 p.2 * (u p.2).im : ℝ) : ℂ))
      (volume.prod volume) := (hrr.add hii).ofReal
  have hB : Integrable (fun p : ℝ × ℝ =>
      (((u p.1).re * k p.1 p.2 * (u p.2).im -
        (u p.1).im * k p.1 p.2 * (u p.2).re : ℝ) : ℂ) * Complex.I)
      (volume.prod volume) := (hri.sub hir).ofReal.mul_const Complex.I
  have hcross :
      (∫ p : ℝ × ℝ, (u p.1).re * k p.1 p.2 * (u p.2).im ∂volume.prod volume) =
      ∫ p : ℝ × ℝ, (u p.1).im * k p.1 p.2 * (u p.2).re ∂volume.prod volume := by
    calc
      _ = ∫ p : ℝ × ℝ, (u p.2).re * k p.2 p.1 * (u p.1).im
          ∂volume.prod volume :=
        (integral_prod_swap
          (fun p : ℝ × ℝ => (u p.1).re * k p.1 p.2 * (u p.2).im)).symm
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => by dsimp; rw [hsymm p.2 p.1]; ring)
  rw [complexKernelQuadratic_eq_product (integrable_complexKernel_product hk hu hus)]
  simp_rw [complexKernel_product_decomposition]
  rw [integral_add hA hB,
    integral_complex_ofReal, integral_mul_const, integral_complex_ofReal,
    integral_add hrr hii, integral_sub hri hir, hcross, sub_self]
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  rw [realKernelQuadratic, realKernelQuadratic,
    realKernelBilinear_eq_product hrr, realKernelBilinear_eq_product hii]

/-- In particular the actual complex form is real, and its real part is the
sum of the two actual real forms. -/
theorem complexKernelQuadratic_re_im
    {k : ℝ → ℝ → ℝ} {u : ℝ → ℂ} {R : ℝ}
    (hk : Continuous (Function.uncurry k))
    (hsymm : ∀ x y, k x y = k y x)
    (hu : Integrable u) (hus : ∀ x ∉ Icc (-R) R, u x = 0) :
    (complexKernelQuadratic k u).im = 0 ∧
      (complexKernelQuadratic k u).re =
        realKernelQuadratic k (fun x => (u x).re) +
        realKernelQuadratic k (fun x => (u x).im) := by
  rw [complexKernelQuadratic_eq_realKernelQuadratic_re_add_im hk hsymm hu hus]
  exact ⟨rfl, rfl⟩

/-- Conditional positivity passes from real mean-zero L2 tests to complex
mean-zero tests whose real and imaginary parts are square-integrable.
All hypotheses concern the same support window and the same actual kernel. -/
theorem complexKernelQuadratic_nonneg_of_real_meanZero_nonneg
    {k : ℝ → ℝ → ℝ} {R : ℝ}
    (hk : Continuous (Function.uncurry k))
    (hsymm : ∀ x y, k x y = k y x)
    (hpos : ∀ f : ℝ → ℝ, Integrable f →
      Integrable (fun x => f x ^ 2) →
      (∀ x ∉ Icc (-R) R, f x = 0) → (∫ x, f x) = 0 →
      0 ≤ realKernelQuadratic k f)
    {u : ℝ → ℂ} (hu : Integrable u)
    (hur2 : Integrable (fun x => (u x).re ^ 2))
    (hui2 : Integrable (fun x => (u x).im ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0)
    (hu0 : (∫ x, u x) = 0) :
    (complexKernelQuadratic k u).im = 0 ∧
      0 ≤ (complexKernelQuadratic k u).re := by
  have hrs : ∀ x ∉ Icc (-R) R, (u x).re = 0 := by
    intro x hx; simp [hus x hx]
  have his : ∀ x ∉ Icc (-R) R, (u x).im = 0 := by
    intro x hx; simp [hus x hx]
  have hr0 : (∫ x, (u x).re) = 0 := by
    calc
      _ = (∫ x, u x).re := integral_re hu
      _ = 0 := by rw [hu0]; rfl
  have hi0 : (∫ x, (u x).im) = 0 := by
    calc
      _ = (∫ x, u x).im := integral_im hu
      _ = 0 := by rw [hu0]; rfl
  obtain ⟨him, hre⟩ := complexKernelQuadratic_re_im hk hsymm hu hus
  refine ⟨him, ?_⟩
  rw [hre]
  exact add_nonneg (hpos _ hu.re hur2 hrs hr0) (hpos _ hu.im hui2 his hi0)

end RiemannResearch.Analysis
