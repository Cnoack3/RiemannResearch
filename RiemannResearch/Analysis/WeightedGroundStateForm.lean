/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ZeroSamplingQuadratic

/-!
# Weighted ground-state identity for finite signed complex forms

Source: the exact graph-energy requirement in the user-requested actual
hyperbolic lower-bound analysis (2026-10-05). This finite polarization
argument applies to arbitrary real symmetric kernels. Its actual full
prime-power consumer is ActualHyperbolicGramLowerBounds. No arithmetic
or analytic hypothesis is introduced here.
-/

noncomputable section
open scoped BigOperators InnerProductSpace

namespace RiemannResearch.Analysis.ZeroSamplingQuadratic
theorem symmetric_real_form_groundState {ι : Type*} [Fintype ι]
    (W : ι → ι → ℝ) (hW : ∀ i j, W i j = W j i) (b : ι → ℂ) :
    (form Finset.univ (fun i j => (W i j : ℂ)) b).re =
      (∑ i, (∑ j, W i j)*‖b i‖^2) -
        (1/2 : ℝ)*∑ i, ∑ j, W i j*‖b i-b j‖^2 := by
  classical
  have hq : (form Finset.univ (fun i j => (W i j : ℂ)) b).re =
      ∑ i, ∑ j, W i j*(b i*star (b j)).re := by
    unfold form
    simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    ring
  have hswap : (∑ i, ∑ j, W i j*‖b j‖^2) = ∑ i, ∑ j, W i j*‖b i‖^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hW j i]
  have hdiag : (∑ i, ∑ j, W i j*‖b i‖^2) =
      ∑ i, (∑ j, W i j)*‖b i‖^2 := by
    simp only [Finset.sum_mul]
  have hdouble : 2*(form Finset.univ (fun i j => (W i j : ℂ)) b).re =
      (∑ i, ∑ j, W i j*‖b i‖^2) +
        (∑ i, ∑ j, W i j*‖b j‖^2) -
        (∑ i, ∑ j, W i j*‖b i-b j‖^2) := by
    rw [hq]
    calc
      _ = ∑ i, ∑ j, W i j*(2*(b i*star (b j)).re) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i, ∑ j, W i j*(‖b i‖^2+‖b j‖^2-‖b i-b j‖^2) := by
        simp_rw [edge_identity]
      _ = _ := by
        simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hswap, hdiag] at hdouble
  linarith

theorem weighted_groundState_identity {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (hA : ∀ i j, A i j = A j i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (f : ι → ℂ) :
    (form Finset.univ (fun i j => (A i j : ℂ)) f).re =
      (∑ i, ((∑ j, A i j*w j)/w i)*‖f i‖^2) -
        (1/2 : ℝ)*∑ i, ∑ j,
          A i j*w i*w j*‖f i/(w i : ℂ)-f j/(w j : ℂ)‖^2 := by
  classical
  let W : ι → ι → ℝ := fun i j => A i j*w i*w j
  let b : ι → ℂ := fun i => f i/(w i : ℂ)
  have hwC (i : ι) : (w i : ℂ) ≠ 0 := by exact_mod_cast (hw i).ne'
  have hW (i j : ι) : W i j = W j i := by
    dsimp [W]; rw [hA i j]; ring
  have hform : form Finset.univ (fun i j => (W i j : ℂ)) b =
      form Finset.univ (fun i j => (A i j : ℂ)) f := by
    unfold form
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [W, b]
    change (f i/(w i : ℂ))*star (f j/(w j : ℂ))*
      ((A i j*w i*w j : ℝ) : ℂ) = f i*star (f j)*(A i j : ℂ)
    have hdiv : star (f j/(w j : ℂ)) = star (f j)/(w j : ℂ) := by
      simp [star_div]
    rw [hdiv]
    push_cast
    field_simp [hwC i, hwC j]
  have hnorm (i : ι) : ‖b i‖^2 = ‖f i‖^2/(w i)^2 := by
    dsimp [b]
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hrow (i : ι) : (∑ j, W i j) = w i*(∑ j, A i j*w j) := by
    dsimp [W]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hdiag : (∑ i, (∑ j, W i j)*‖b i‖^2) =
      ∑ i, ((∑ j, A i j*w j)/w i)*‖f i‖^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hrow, hnorm]
    field_simp [(hw i).ne']
  have h := symmetric_real_form_groundState W hW b
  rw [hform, hdiag] at h
  simpa only [W, b] using h
end RiemannResearch.Analysis.ZeroSamplingQuadratic
